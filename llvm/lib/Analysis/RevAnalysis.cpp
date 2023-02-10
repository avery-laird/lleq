#include "llvm/Analysis/RevAnalysis.h"
#include "z3++.h"
#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/Triple.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/CFG.h"
#include "llvm/Analysis/Delinearization.h"
#include "llvm/Analysis/DemandedBits.h"
#include "llvm/Analysis/IVDescriptors.h"
#include "llvm/Analysis/LoopAccessAnalysis.h"
#include "llvm/Analysis/LoopNestAnalysis.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/Operator.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include <chrono>
#include <cvc5/cvc5.h>
#include <fstream>
#include <sstream>

#define DEBUG_TYPE "rev-analysis"

using namespace std::chrono;

using namespace llvm;
using namespace z3;
using namespace cvc5;

static cl::opt<bool>
    EnableLifting("enable-lifting", cl::init(true), cl::Hidden,
                  cl::desc("Enable lifting of non-affine kernels."));


static void GetLiveIns(Loop *L, SmallPtrSet<Value *, 4> &LiveIns) {
  for (auto *BB : L->getBlocks()) {
    for (auto &I : *BB) {
      for (auto &O : I.operands()) {
        // store the whole instruction and not just the operand so
        // that the type information is known (for example loads
        // and GEP on opaque pointers) https://llvm.org/docs/OpaquePointers.html
        if (auto *Inst = dyn_cast<Instruction>(&O))
          if (!L->contains(Inst))
            LiveIns.insert(&I);
        if (auto *Arg = dyn_cast<Argument>(&O))
          LiveIns.insert(&I);
      }
    }
  }

  LLVM_DEBUG(dbgs() << "Found " << LiveIns.size() << " live ins:\n");
  for (auto *V : LiveIns) {
    LLVM_DEBUG(dbgs() << *V << "\n");
  }
}

static void GetLiveOuts(Loop *L, SmallPtrSet<Value *, 4> &LiveOuts) {
  SmallPtrSet<Value *, 5> BasePtrs;
  SmallVector<BasicBlock *> ExitBlocks;
  L->getExitBlocks(ExitBlocks);
  for (auto *BB : ExitBlocks)
    for (auto &I : *BB)
      if (auto *PN = dyn_cast<PHINode>(&I))
        LiveOuts.insert(&I);
  // TODO: considering the StoreInst
  for (auto *BB : L->getBlocks())
    for (auto &I : *BB) {
      if (isa<StoreInst>(&I)) {
        // get the GEP
        if (auto *GEP = dyn_cast<GEPOperator>(getLoadStorePointerOperand(&I))) {
          if (BasePtrs.count(GEP->getPointerOperand()))
            continue;
          LiveOuts.insert(&I); // TODO replace everything with GEPs
          BasePtrs.insert(GEP->getPointerOperand());
        }
      }
    }
}

// TODO all based on pointers, so dangerous if MakTerm is run
// after the mapping

// keep track of all terminals used *anywhere* by *any* loop.
// there must be at most 1 Z3 expr and/or 1 CVC5 term associated
// with any terminal.
class TerminalMap {
public:
  TerminalMap(context &c) : c(c), Z3Symbols(c), Z3Functions(c) {}

  expr setZ3(Value *V, expr const &Expr) {
    Z3Symbols.push_back(Expr);
    Z3Map[V] = Z3Symbols.size() - 1;
    return getZ3(V);
  }

  func_decl setZ3Fun(Value *V, func_decl const &Fun) {
    Z3Functions.push_back(Fun);
    Z3FunMap[V] = Z3Functions.size() - 1;
    return Z3Functions.back();
  }

  expr getZ3(Value *V) { return Z3Symbols[Z3Map[V]]; }
  func_decl getZ3Fun(Value *V) { return Z3Functions[Z3FunMap[V]]; }

  bool countZ3(Value *V) { return Z3Map.count(V); }

  context &ctxt() { return c; }

private:
  context &c;
  expr_vector Z3Symbols;
  func_decl_vector Z3Functions;
  std::vector<Term> CVCSymbols;

  DenseMap<Value *, unsigned> Z3Map;
  DenseMap<Value *, unsigned> Z3FunMap;
  DenseMap<Value *, unsigned> CVC5Map;
};

template <typename ExprTy, typename SortTy> class MakeSMT {
protected:
  Loop *L = nullptr;
  LoopInfo *LI = nullptr;
  ScalarEvolution &SE;
  LoopNest *LN = nullptr;
  SmallPtrSet<Value *, 5> BuildRecursive;

public:
  MakeSMT(TerminalMap &Map, ScalarEvolution &SE) : SE(SE), Map(Map) {}

  ExprTy FromVal(Value *V) {
    // update the current loop
    if (count(V))
      return get(V);
    // either a constant, or an instruction.
    auto Dispatch = [&](Value *V) {
      if (auto *Const = dyn_cast<Constant>(V))
        return FromConst(Const);
      if (isa<Argument>(V))
        return FromPHIorArg(V);

      Instruction *I = dyn_cast<Instruction>(V);
      if (I == nullptr)
        llvm_unreachable("unsupported value type.");

      switch (I->getOpcode()) {
      case Instruction::Load:
      case Instruction::Store:
        return FromLoadStore(I);
      case Instruction::PHI:
        return FromPHIorArg(I);
      case Instruction::FCmp:
      case Instruction::ICmp:
        return FromCmpInst(static_cast<CmpInst *>(I));
      case Instruction::Call:
        return FromCallInst(static_cast<CallInst *>(I));

#define HANDLE_CAST_INST(NUM, OPCODE, CLASS)                                   \
  case Instruction::OPCODE:                                                    \
    return FromCastInst(static_cast<CastInst *>(I));
#define HANDLE_BINARY_INST(NUM, OPCODE, CLASS)                                 \
  case Instruction::OPCODE:                                                    \
    return FromBinOp(static_cast<BinaryOperator *>(I));
#include "llvm/IR/Instruction.def"

      default:
        llvm_unreachable("unsupported opcode.");
      }
    };

    return set(V, Dispatch(V));
  }

protected:
  TerminalMap &Map;
  struct GEPTy {
    ExprTy Base;
    ExprTy Offset;
  };

  virtual unsigned count(Value *V) = 0;
  virtual ExprTy get(Value *V) = 0;
  virtual ExprTy set(Value *V, const ExprTy &) = 0;

  virtual ExprTy FromConst(Constant *V) = 0;
  virtual ExprTy FromLoadStore(Value *V) = 0;
  virtual GEPTy FromGEP(GEPOperator *V) = 0;
  virtual ExprTy FromCastInst(CastInst *V) = 0;
  virtual ExprTy FromPHIorArg(Value *V) = 0;
  virtual ExprTy FromBinOp(BinaryOperator *V) = 0;
  virtual ExprTy FromCmpInst(CmpInst *V) = 0;
  virtual ExprTy FromCallInst(CallInst *V) = 0;

  virtual SortTy ToSort(Value *V) = 0;
  virtual SortTy ToSort(Type *T) = 0;
};

class MakeZ3 : public MakeSMT<expr, z3::sort> {
public:
  MakeZ3(TerminalMap &Map, ScalarEvolution &SE, context &c)
      : MakeSMT(Map, SE), c(c) {}

  z3::sort ToSort(Value *V) override {
    auto *T = V->getType();
    switch (T->getTypeID()) {
    default:
      llvm_unreachable("unsupported LLVM type.");
    case Type::TypeID::IntegerTyID:
    case Type::TypeID::DoubleTyID:
      return ToSort(T);
    case Type::TypeID::PointerTyID:
      // try to find a use that we can infer the type from
      for (auto *Use : V->users()) {
        if ((isa<LoadInst>(Use) || isa<StoreInst>(Use)))
          return c.array_sort(c.int_sort(), ToSort(getLoadStoreType(Use)));
        if (auto *GEP = dyn_cast<GEPOperator>(Use))
          return c.array_sort(c.int_sort(),
                              ToSort(GEP->getSourceElementType()));
      }
      llvm_unreachable("couldn't infer the type of the pointer.");
    }
  }

  z3::sort ToSort(Type *T) override {
    unsigned Mantissa, Exponent;
    switch (T->getTypeID()) {
    default:
      llvm_unreachable("unsupported LLVM type.");
    case Type::TypeID::IntegerTyID:
      return c.int_sort();
    case Type::TypeID::DoubleTyID:
      // TODO remove this debug
      Mantissa = APFloat::semanticsPrecision(T->getFltSemantics());
      Exponent = APFloat::semanticsSizeInBits(T->getFltSemantics()) - Mantissa;
      //      return c.fpa_sort(Exponent, Mantissa);
      return c.int_sort();
    }
  }

  GEPTy FromGEP(GEPOperator *GEP) override {
    assert(GEP->getNumIndices() == 1);
    // make the array if it doesn't exist
    if (!count(GEP->getPointerOperand())) {
      // TODO assume 1d memory accesses
      z3::sort ArraySort = c.array_sort(ToSort(GEP->getOperand(1)),
                                        ToSort(GEP->getResultElementType()));
      set(GEP->getPointerOperand(),
          c.constant(GEP->getPointerOperand()->getName().data(), ArraySort));
    }
    expr Base = get(GEP->getPointerOperand());
    expr Offset = FromVal(GEP->getOperand(1));
    return {Base, Offset};
  }

protected:
  context &c;

  unsigned count(Value *V) override { return Map.countZ3(V); }

  expr get(Value *V) override { return Map.getZ3(V); }

  expr set(Value *V, const expr &Expr) override { return Map.setZ3(V, Expr); }

  expr FromConst(Constant *V) override {
    APSInt Result(64, false); // 64 bits wide, possibly signed
    bool isExact;
    if (isa<UndefValue>(V))
      return c.int_val(0);

    switch (V->getType()->getTypeID()) {
    case Type::TypeID::IntegerTyID:
      return c.int_val(dyn_cast<ConstantInt>(V)->getSExtValue());
    case Type::TypeID::DoubleTyID:
      // TODO remove this debug hack
      dyn_cast<ConstantFP>(V)->getValue().convertToInteger(
          Result, APFloatBase::rmNearestTiesToEven, &isExact);
      return c.int_val(Result.getSExtValue());
      //      return
      //      c.fpa_val(dyn_cast<ConstantFP>(V)->getValue().convertToDouble());
    default:
      llvm_unreachable("unsupported constant type");
    }
  }

  expr FromLoadStore(Value *V) override {
    auto *GEP = dyn_cast<GEPOperator>(getLoadStorePointerOperand(V));
    // eg. y[i]
    GEPTy ArrayAddr = FromGEP(GEP); // (tuple base offset)
    // if store, y[i] = ...  (store)
    // if load %0 = y[i]     (select)
    expr Expr(c);
    if (auto *Store = dyn_cast<StoreInst>(V))
      return store(ArrayAddr.Base, ArrayAddr.Offset,
                   FromVal(Store->getValueOperand()));
    return ArrayAddr.Base[ArrayAddr.Offset];
  }

  expr FromCastInst(CastInst *C) override { return FromVal(C->getOperand(0)); }

  expr FromBinOp(BinaryOperator *BinOp) override {
    auto Left = FromVal(BinOp->getOperand(0));
    auto Right = FromVal(BinOp->getOperand(1));
    switch (BinOp->getOpcode()) {
    case BinaryOperator::BinaryOps::Add:
    case BinaryOperator::BinaryOps::FAdd:
      return Left + Right;
    case BinaryOperator::BinaryOps::Mul:
    case BinaryOperator::BinaryOps::FMul:
      return Left * Right;
    case BinaryOperator::BinaryOps::SDiv:
    case BinaryOperator::BinaryOps::FDiv:
    case BinaryOperator::BinaryOps::UDiv:
      return Left / Right;
    case BinaryOperator::BinaryOps::Sub:
    case BinaryOperator::BinaryOps::FSub:
      return Left - Right;
    case BinaryOperator::BinaryOps::And:
      return bv2int(int2bv(64, Left) & int2bv(64, Right), true);
    case BinaryOperator::BinaryOps::Xor:
      return bv2int(int2bv(64, Left) ^ int2bv(64, Right), true);
    case BinaryOperator::BinaryOps::Or:
      return bv2int(int2bv(64, Left) | int2bv(64, Right), true);
    case BinaryOperator::BinaryOps::SRem:
      return Left % Right; // TODO this doesn't map exactly, may be some bugs
    case BinaryOperator::BinaryOps::Shl:
      return bv2int(shl(int2bv(64, Left), int2bv(64, Right)), true);
    case BinaryOperator::BinaryOps::LShr:
      return bv2int(lshr(int2bv(64, Left), int2bv(64, Right)), true);
    case BinaryOperator::BinaryOps::AShr:
      return bv2int(ashr(int2bv(64, Left), int2bv(64, Right)), true);
    default:
      llvm_unreachable("unsupported binop type.");
    }
  }

  expr FromCmpInst(CmpInst *Cmp) override {
    auto Left = FromVal(Cmp->getOperand(0));
    auto Right = FromVal(Cmp->getOperand(1));
    switch (Cmp->getPredicate()) {
    default:
      llvm_unreachable("unsupported predicate type.");
    case CmpInst::ICMP_SLT:
    case CmpInst::ICMP_ULT:
      return Left < Right;
    case CmpInst::ICMP_SGT:
    case CmpInst::ICMP_UGT:
      return Left > Right;
    case CmpInst::ICMP_EQ:
    case CmpInst::FCMP_OEQ:
      return Left == Right;
    }
  }

  expr FromCallInst(CallInst *CI) override {
    auto *F = CI->getCalledFunction();
    if (F && F->getIntrinsicID() == Intrinsic::fmuladd) {
      // a*b + c
      expr A = FromVal(CI->getOperand(0));
      expr B = FromVal(CI->getOperand(1));
      expr C = FromVal(CI->getOperand(2));
      //      return fma(A, B, C, c.fpa_rounding_mode());
      // TODO remove this debug hack
      return A * B + C;
    }
    llvm_unreachable("arbitrary functions aren't supported.");
  }

  expr FromPHIorArg(Value *V) override {
    return c.constant(V->getName().str().c_str(), ToSort(V));
  }
};

class SSA2Func {
  using ConverterTy = MakeZ3;
  using PhiMapTy = DenseMap<PHINode *, Value *>;
  using CycleTy =
      SmallVector<std::pair<const BasicBlock *, const BasicBlock *>>;

public:

  SSA2Func(context &Ctx, DominatorTree *DT, ConverterTy *Converter,
           Value *LiveOut)
      : Ctx(Ctx), BB2Func(Ctx), DT(DT), Converter(Converter), Range(Ctx),
        Output(Ctx), Projs(Ctx) {
    if (auto *GEP =
            dyn_cast<GEPOperator>(getLoadStorePointerOperand(LiveOut))) {
      auto Tuple = Converter->FromGEP(GEP);
      Range = Tuple.Base.get_sort();
      Output = Tuple.Base;
    } else {
      llvm_unreachable("other liveout types aren't supported right now.");
    }
  }

  SSA2Func(context &Ctx, DominatorTree *DT, ConverterTy *Converter,
           SmallPtrSetImpl<Value *> &LiveOut)
      : Ctx(Ctx), BB2Func(Ctx), DT(DT), Converter(Converter), Range(Ctx),
        Output(Ctx), Projs(Ctx) {
    // range is a tuple sort
    // output is the tuple itself
    std::vector<z3::sort> TupleSorts;
    expr_vector Elems(Ctx);
    for (auto *V : LiveOut) {
      if (auto *GEP = dyn_cast<GEPOperator>(V)) {
        auto Tuple = Converter->FromGEP(GEP);
        Elems.push_back(Tuple.Base);
      } else {
        Elems.push_back(Converter->FromVal(V));
      }
    }
    for (auto E : Elems)
      TupleSorts.push_back(E.get_sort());
    //    const char * names[] = { "first", "second" };
    std::vector<const char *> Names;
    SavedNames.resize(Elems.size());
    for (unsigned i = 0; i < Elems.size(); ++i) {
      SavedNames[i] = std::string("get_" + std::to_string(i));
      Names.push_back(SavedNames[i].c_str());
    }
    func_decl MkTuple = Ctx.tuple_sort("ret", LiveOut.size(), Names.data(),
                                       TupleSorts.data(), Projs);
    Output = MkTuple(Elems);
    Range = Output.get_sort();
  }

  func_decl getNth(unsigned i) { return Projs[i]; }

  func_decl fromFunction(Function *F) {
    BasicBlock *BB = &F->getEntryBlock();
    std::vector<Value *> FArgs;
    for (auto &Use : F->args())
      FArgs.push_back(&Use);
    Scopes[BB] = makeScope(BB, FArgs);
    makeScopes(BB);
    for (auto &NewBB : *F)
      makeCall(&NewBB);
    return BB2Func.getZ3Fun(BB);
  }

  func_decl straightlineFromFunction(Function *F, CycleTy *C) {
    Cycles = C;
    func_decl Translate = fromFunction(F);
    PhiMap = nullptr;
    Cycles = nullptr;
    return Translate;
  }

  void makeScopes(BasicBlock *BB) {
    auto &Scope = Scopes[BB];
    // make domain
    std::vector<z3::sort> Domain;
    for (auto *V : Scope)
      Domain.push_back(Converter->FromVal(V).get_sort());
    auto Name = BB->getName().str();
    if (Cycles != nullptr)
      Name += ".noloop";
    BB2Func.setZ3Fun(
        BB, Ctx.recfun(Name.c_str(), Domain.size(), Domain.data(), Range));
    LLVM_DEBUG({
      dbgs() << BB->getNameOrAsOperand() << ": ";
      for (auto S : Domain)
        dbgs() << S.to_string() << " -> ";
      dbgs() << Range.to_string() << "\n";
    });
    auto *Node = DT->getNode(BB);
    for (auto *N : *Node) {
      auto *NewBB = N->getBlock();
      Scopes[NewBB] = makeScope(NewBB, Scope);
      makeScopes(NewBB);
    }
  }

  void makeCall(BasicBlock *BB) {
    expr_vector Scope(Ctx);
    // add to the current scope
    for (auto *V : Scopes[BB])
      Scope.push_back(Converter->FromVal(V));

    if (auto *Ret = dyn_cast<ReturnInst>(BB->getTerminator())) {
      Ctx.recdef(BB2Func.getZ3Fun(BB), Scope, Output);
      LLVM_DEBUG({
        dbgs() << BB->getNameOrAsOperand() << ", [";
        for (unsigned i = 0; i < Scope.size() - 1; ++i)
          dbgs() << Scope[i].to_string() << ", ";
        dbgs() << Scope.back().to_string() << "]\n";
        dbgs() << Output.to_string() << "\n";
      });
      return;
    }

    // after setting scopes, start wiring functions together
    auto *Br = dyn_cast<BranchInst>(BB->getTerminator());
    assert(
        Br != nullptr &&
        "only basic blocks terminating in a branch instruction are supported");
    expr_vector Calls(Ctx);
    for (auto *Block : Br->successors()) {
      expr_vector LocalScope(Ctx);
      for (auto *V : Scopes[Block]) {
        if (auto *Phi = dyn_cast<PHINode>(V)) {
          //          if (PhiMap != nullptr && PhiMap->count(Phi)) {
          //            // PhiMap is only not-null when we want straightline
          //            code expr Expr =
          //            Converter->FromVal(PhiMap->lookup(Phi)); for (auto
          //            &Elems : *PhiMap) {
          //              expr_vector Src(Ctx), Dst(Ctx);
          //              Src.push_back(Converter->FromVal(Elems.getFirst()));
          //              Dst.push_back(Converter->FromVal(Elems.getSecond()));
          //              Expr = Expr.substitute(Src, Dst);
          //            }
          //            LocalScope.push_back(Expr);
          //            continue;
          //          }
          if ((PhiMap == nullptr ||
               (PhiMap != nullptr && !PhiMap->count(Phi))) &&
              Phi->getBasicBlockIndex(BB) > -1) {
            LocalScope.push_back(
                Converter->FromVal(Phi->getIncomingValueForBlock(BB)));
            continue;
          }
        }
        // otherwise, it MUST be a memory operation.
        // find the corresponding store (in this block):
        bool Found = false;
        for (auto &Inst : *BB) {
          if (auto *Store = dyn_cast<StoreInst>(&Inst)) {
            if (getPointerOperand(getLoadStorePointerOperand(Store)) == V) {
              LocalScope.push_back(Converter->FromVal(Store));
              Found = true;
              break;
            }
          }
        }
        if (!Found)
          LocalScope.push_back(Converter->FromVal(V));
      }
      Calls.push_back(BB2Func.getZ3Fun(Block)(LocalScope));
    }

    expr Body(Ctx);

    auto IsTarget = [&Br](unsigned S) {
      return
          [&Br, S](auto &Elem) { return Elem.second == Br->getSuccessor(S); };
    };
    if (Br->isUnconditional())
      Body = Calls[0];
    else if (Cycles != nullptr && std::find_if(Cycles->begin(), Cycles->end(),
                                               IsTarget(0)) != Cycles->end()) {
      Body = Calls[0];
    } else if (Cycles != nullptr &&
               std::find_if(Cycles->begin(), Cycles->end(), IsTarget(1)) !=
                   Cycles->end()) {
      Body = Calls[1];
    } else {
      Body = ite(Converter->FromVal(Br->getCondition()), Calls[1], Calls[0]);
    }


    Ctx.recdef(BB2Func.getZ3Fun(BB), Scope, Body);

    LLVM_DEBUG({
      dbgs() << BB->getNameOrAsOperand() << ", [";
      for (unsigned i = 0; i < Scope.size() - 1; ++i)
        dbgs() << Scope[i].to_string() << ", ";
      dbgs() << Scope.back().to_string() << "]\n";
      dbgs() << Body.to_string() << "\n";
    });
  }

  func_decl operator[](Value *V) { return BB2Func.getZ3Fun(V); }

  DenseMap<Value *, std::vector<Value *>> Scopes;

private:
  std::vector<Value *> makeScope(BasicBlock *BB, std::vector<Value *> Prefix) {
    for (auto &Inst : *BB) {
      if (auto *Phi = dyn_cast<PHINode>(&Inst))
        Prefix.push_back(Phi);
      else
        break;
    }
    return Prefix;
  }
  context &Ctx;
  TerminalMap BB2Func;
  DominatorTree *DT;
  ConverterTy *Converter;
  z3::sort Range;
  expr Output;
  func_decl_vector Projs;
  std::vector<std::string> SavedNames;
  PhiMapTy *PhiMap = nullptr;
  CycleTy *Cycles = nullptr;
};


SSA2Func ParseInputFile(StringRef Path, StringRef FunctionName,
                        LLVMContext &Context, ScalarEvolution &SE, context &Ctx,
                        MakeZ3 &Converter, std::unique_ptr<Module> &Module) {
  llvm::SMDiagnostic Err;
  Module = llvm::parseIRFile(Path, Err, Context);
  assert(Module && "couldn't parse kernel.");

  Function *F = Module->getFunction(FunctionName);

  DominatorTree DT(*F);
  LoopInfo LI(DT);
  LoopNest LN(*LI.getTopLevelLoops()[0], SE);
  auto *OuterLoop = &LN.getOutermostLoop();

  SmallPtrSet<Value *, 5> Stores;
  for (BasicBlock *BB : OuterLoop->blocks()) {
    for (Instruction &Inst : *BB) {
      if (auto *Store = dyn_cast<StoreInst>(&Inst))
        Stores.insert(getLoadStorePointerOperand(Store));
    }
  }

  SSA2Func File(Ctx, &DT, &Converter, Stores);
  File.fromFunction(F);
  // let's try something interesting...
  solver Slv(Ctx);
  expr n = Converter.FromVal(F->getArg(0));
  expr m = Converter.FromVal(F->getArg(1));
  expr A = Converter.FromVal(F->getArg(2));
  expr rptr = Converter.FromVal(F->getArg(3));
  expr cols = Converter.FromVal(F->getArg(4));
  expr vals = Converter.FromVal(F->getArg(5));
  auto mki = [&](int i) { return Ctx.int_val(i); };
  Slv.add(n == 2);
  Slv.add(m == 2);
  Slv.add(A[mki(0)] == 0);
  Slv.add(A[mki(1)] == 1);
  Slv.add(A[mki(2)] == 1);
  Slv.add(A[mki(3)] == 0);
  Slv.add(forall(n, rptr[n] == 0));
  auto Result = Slv.check();
  if (Result == z3::sat) {
    auto Model = Slv.get_model();
    std::vector<expr> Args = {n, m, A, rptr, cols, vals};
    auto Output = File[&F->getEntryBlock()](Args.size(), Args.data());
    //    LLVM_DEBUG({
    dbgs() << "Concrete Test output: \n";
    std::vector<unsigned> lens = {2, 2, 3};
    for (int idx : {0, 1, 2}) {
      auto array = Model.eval(File.getNth(idx)(Output).simplify());
      for (int i = 0; i < lens[idx]; ++i) {
        auto elem = Model.eval(array[mki(i)].simplify());
        if (elem.is_fpa())
          dbgs() << Z3_get_numeral_string(Ctx, elem) << " ";
        else
          dbgs() << elem.to_string() << " ";
      }
      dbgs() << "\n";
    }
    //    });
  }
  return File;
}


class Properties {
protected:
  struct Prop {
    std::string Name;
    std::function<bool(Value *)> Check;
    SmallPtrSetImpl<Value *> *Set = nullptr;
  };
  std::vector<SmallPtrSet<Value *, 5>> Sets;

public:
  std::vector<Prop> Props;

  Properties(LoopNest &LN, ScalarEvolution &SE) {
    Props = {
        {"readonly",
         [](Value *V) {
           if (V->getType()->getTypeID() != Type::TypeID::PointerTyID)
             return false;
           // V is never the ptr operand for any store
           std::vector<Value *> Stack;
           SmallPtrSet<Value *, 10> Visited;
           DenseMap<Value *, Value *> ParentOf;
           Stack.push_back(V);
           while (!Stack.empty()) {
             Value *E = Stack.back();
             Visited.insert(E);
             Stack.pop_back();
             if (auto *Store = dyn_cast<StoreInst>(E))
               if (Store->getPointerOperand() == ParentOf[E])
                 return false;
             for (auto *U : E->users())
               if (!Visited.contains(U)) {
                 Stack.push_back(U);
                 ParentOf[U] = E;
               }
           }
           return true;
         }},
        {"int",
         [](Value *V) {
           return V->getType()->getTypeID() == Type::TypeID::IntegerTyID;
         }},
        {"array",
         [](Value *V) {
           return V->getType()->getTypeID() == Type::TypeID::PointerTyID;
         }},
        {"as_address",
         [](Value *V) {
           if (V->getType()->getTypeID() != Type::TypeID::PointerTyID)
             return false;
           // V is a GEP ptr operand
           // -> used in a load
           // -> used as a GEP index
           std::vector<Value *> Stack;
           SmallPtrSet<Value *, 10> Visited;
           DenseMap<Value *, Value *> ParentOf;
           Stack.push_back(V);
           Value *GEPPtr = nullptr;
           Value *LoadUser = nullptr;
           Value *GEPIdx = nullptr;
           while (!Stack.empty()) {
             Value *E = Stack.back();
             Visited.insert(E);
             Stack.pop_back();
             if (auto *GEP = dyn_cast<GEPOperator>(E)) {
               if (GEP->getPointerOperand() == V)
                 GEPPtr = GEP;
               else if (GEPPtr && LoadUser &&
                        (*GEP->indices().begin() == ParentOf[E]))
                 GEPIdx = GEP;
             }
             if (auto *Load = dyn_cast<LoadInst>(E))
               if (GEPPtr && Load->getPointerOperand() == GEPPtr)
                 LoadUser = Load;
             if (GEPPtr && LoadUser && GEPIdx)
               return true;
             for (auto *U : E->users())
               if (!Visited.contains(U)) {
                 Stack.push_back(U);
                 ParentOf[U] = E;
               }
           }
           return false;
         }},
        {"direct_access",
         [](Value *V) {
           if (V->getType()->getTypeID() != Type::TypeID::PointerTyID)
             return false;
           // do GEPs have only 1 dimension?
           for (auto *U : V->users()) {
             if (auto *GEP = dyn_cast<GEPOperator>(U)) {
               // get the index
               if (GEP->getNumIndices() > 1)
                 llvm_unreachable(
                     "GEPOperators with multiple indices are not supported.");
               auto &Idx = *GEP->indices().begin();
               Instruction *Inst = dyn_cast<Instruction>(&Idx);
               while (Inst != nullptr &&
                      (isa<SExtInst>(Inst) || isa<ZExtInst>(Inst) ||
                       isa<BitCastInst>(Inst))) {
                 Instruction *Tmp = dyn_cast<Instruction>(Inst->getOperand(0));
                 if (Tmp == nullptr)
                   break;
                 Inst = Tmp;
               }
               if (getLoadStorePointerOperand(Inst))
                 return false;
             }
           }
           return true;
         }},
        {"loop_bounds", [&](Value *V) {
           if (V->getType()->getTypeID() != Type::TypeID::PointerTyID)
             return false;
           for (const Loop *L : LN.getLoops()) {
             auto Bounds = L->getBounds(SE);
             LoadInst *LowInstr =
                 dyn_cast<LoadInst>(&Bounds->getInitialIVValue());
             LoadInst *UpInstr = dyn_cast<LoadInst>(&Bounds->getFinalIVValue());
             if (!LowInstr || !UpInstr)
               continue;
             Value *LowPtr = getLoadStorePointerOperand(LowInstr);
             Value *UpPtr = getLoadStorePointerOperand(UpInstr);
             auto *LowGEP = dyn_cast<GetElementPtrInst>(LowPtr);
             auto *HighGEP = dyn_cast<GetElementPtrInst>(UpPtr);
             if (!LowGEP || !HighGEP)
               continue;
             Value *LowPtrBase = LowGEP->getPointerOperand();
             Value *HighPtrBase = HighGEP->getPointerOperand();
             const SCEV *LowIndex = SE.getSCEV(LowGEP->getOperand(1));
             const SCEV *HighIndex = SE.getSCEV(HighGEP->getOperand(1));
             const SCEV *OffsetIndex = SE.getMinusSCEV(HighIndex, LowIndex);
             if (LowPtrBase != HighPtrBase)
               continue;
             if (LowPtrBase == V)
               return true;
           }
           return false;
         }}};
  }

  void buildSets(std::vector<Value *> &Vars) {
    Sets.resize(Props.size());
    for (unsigned i = 0; i < Props.size(); ++i) {
      for (auto *V : Vars) {
        if (Props[i].Check(V))
          Sets[i].insert(V);
      }
      Props[i].Set = &Sets[i];
    }
  }
};

class Kernel {
public:
  Kernel(std::string Name, std::string SparseName)
      : Name(Name), SparseName(SparseName) {}

  virtual func_decl makeKernel(context &Ctx, func_decl &A,
                               expr_vector const &Ins) = 0;
  virtual func_decl makeKernelNoLoop(context &Ctx, expr &A,
                                     expr_vector const &Ins) = 0;

  std::string Name;
  std::string SparseName;
};

class GEMV : public Kernel {
public:
  GEMV() : Kernel("GEMV", "SPMV") {}

  func_decl makeKernel(context &Ctx, func_decl &A,
                       expr_vector const &Ins) override {
    expr y = Ins[0];
    expr x = Ins[1];
    expr n = Ctx.int_const("n");
    expr m = Ctx.int_const("m");
    expr i = Ctx.int_const("i");
    expr j = Ctx.int_const("j");
    expr_vector ArgsGemv(Ctx), ArgsDot(Ctx);

    ArgsGemv.push_back(i); // lower bound
    ArgsGemv.push_back(n);
    ArgsGemv.push_back(j); // lower bound
    ArgsGemv.push_back(m);

    ArgsDot.push_back(n);
    ArgsDot.push_back(j); // lower bound
    ArgsDot.push_back(m);

    std::vector<z3::sort> GemvSorts = {Ctx.int_sort(), Ctx.int_sort(),
                                       Ctx.int_sort(), Ctx.int_sort()};
    func_decl gemv = Ctx.recfun(Name.c_str(), GemvSorts.size(),
                                GemvSorts.data(), y.get_sort());
    std::vector<z3::sort> DotSorts = {Ctx.int_sort(), Ctx.int_sort(),
                                      Ctx.int_sort()};
    func_decl dot = Ctx.recfun((Name + ".dot").c_str(), DotSorts.size(),
                               DotSorts.data(), y[Ctx.int_val(0)].get_sort());
    Ctx.recdef(gemv, ArgsGemv,
               ite(n < i, y,
                   store(gemv(i, n - 1, j, m), n,
                         gemv(i, n - 1, j, m)[n] + dot(n, j, m - 1))));
    Ctx.recdef(dot, ArgsDot,
               ite(m < j, Ctx.int_val(0), dot(n, j, m - 1) + A(n, m) * x[m]));
    return gemv;
  }

  func_decl makeKernelNoLoop(context &Ctx, expr &A,
                             expr_vector const &Ins) override {
    expr y = Ins[0];
    expr x = Ins[1];
    expr n = Ctx.int_const("n");
    expr m = Ctx.int_const("m");
    expr i = Ctx.int_const("i");
    expr j = Ctx.int_const("j");
    expr_vector ArgsGemv(Ctx), ArgsDot(Ctx);

    ArgsGemv.push_back(i); // lower bound
    ArgsGemv.push_back(n);
    ArgsGemv.push_back(j); // lower bound
    ArgsGemv.push_back(m);

    std::vector<z3::sort> GemvSorts = {Ctx.int_sort(), Ctx.int_sort(),
                                       Ctx.int_sort(), Ctx.int_sort()};
    func_decl gemv = Ctx.recfun((Name + ".noloop").c_str(), GemvSorts.size(),
                                GemvSorts.data(), y.get_sort());
    Ctx.recdef(
        gemv, ArgsGemv,
        ite(n > i,
            ite(m > j, store(y, i, select(y, i) + A[i * m + j] * x[j]), y), y));
    return gemv;
  }
};

class GEMV_reset : public Kernel {
public:
  GEMV_reset() : Kernel("GEMV_reset", "SPMV_reset") {}

  func_decl makeKernel(context &Ctx, func_decl &A,
                       expr_vector const &Ins) override {
    expr y = Ins[0];
    expr x = Ins[1];
    expr n = Ctx.int_const("n");
    expr m = Ctx.int_const("m");
    expr i = Ctx.int_const("i");
    expr j = Ctx.int_const("j");
    expr_vector ArgsGemv(Ctx), ArgsDot(Ctx);

    ArgsGemv.push_back(i); // lower bound
    ArgsGemv.push_back(n);
    ArgsGemv.push_back(j); // lower bound
    ArgsGemv.push_back(m);

    ArgsDot.push_back(n);
    ArgsDot.push_back(j); // lower bound
    ArgsDot.push_back(m);

    std::vector<z3::sort> GemvSorts = {Ctx.int_sort(), Ctx.int_sort(),
                                       Ctx.int_sort(), Ctx.int_sort()};
    func_decl gemv = Ctx.recfun(Name.c_str(), GemvSorts.size(),
                                GemvSorts.data(), y.get_sort());
    std::vector<z3::sort> DotSorts = {Ctx.int_sort(), Ctx.int_sort(),
                                      Ctx.int_sort()};
    func_decl dot = Ctx.recfun((Name + ".dot").c_str(), DotSorts.size(),
                               DotSorts.data(), y[Ctx.int_val(0)].get_sort());
    Ctx.recdef(gemv, ArgsGemv,
               ite(n < i, y, store(gemv(i, n - 1, j, m), n, dot(n, j, m - 1))));
    Ctx.recdef(dot, ArgsDot,
               ite(m < j, Ctx.int_val(0), dot(n, j, m - 1) + A(n, m) * x[m]));
    return gemv;
  }
  func_decl makeKernelNoLoop(context &Ctx, expr &A,
                             expr_vector const &Ins) override {
    expr y = Ins[0];
    expr x = Ins[1];
    expr n = Ctx.int_const("n");
    expr m = Ctx.int_const("m");
    expr i = Ctx.int_const("i");
    expr j = Ctx.int_const("j");
    expr_vector ArgsGemv(Ctx), ArgsDot(Ctx);

    ArgsGemv.push_back(i); // lower bound
    ArgsGemv.push_back(n);
    ArgsGemv.push_back(j); // lower bound
    ArgsGemv.push_back(m);

    std::vector<z3::sort> GemvSorts = {Ctx.int_sort(), Ctx.int_sort(),
                                       Ctx.int_sort(), Ctx.int_sort()};
    func_decl gemv = Ctx.recfun((Name + ".noloop").c_str(), GemvSorts.size(),
                                GemvSorts.data(), y.get_sort());
    Ctx.recdef(
        gemv, ArgsGemv,
        ite(n > i,
            ite(m > j,
                store(y, i, select(store(y, i, 0), i) + A[i * m + j] * x[j]),
                y),
            store(y, i, 0)));
    return gemv;
  }
};

class Format {
protected:
  using MapTy = DenseMap<StringRef, unsigned>;
  using NameMapTy = DenseMap<StringRef, Value *>;

public:
  Format(Properties &Props, z3::context &Ctx, const std::vector<Value *> &Scope,
         z3::solver &Slv, MakeZ3 &Converter, func_decl InputKernel)
      : Props(Props), Ctx(Ctx), Scope(Scope), Slv(Slv), Converter(Converter),
        InputKernel(InputKernel),
        EQUAL(Ctx.constant("EQUAL",
                           Ctx.array_sort(Ctx.int_sort(), Ctx.int_sort()))),
        n(Ctx.int_const("n")), m(Ctx.int_const("m")), nnz(Ctx.int_const("nnz")),
        Model(Ctx) {}

  bool validateMapping() {
    Slv.reset();

    func_decl_vector AllRelations(Ctx);
    for (unsigned i = 0; i < Props.Props.size(); ++i)
      AllRelations.push_back(Ctx.function(Props.Props[i].Name.c_str(),
                                          Ctx.int_sort(), Ctx.bool_sort()));

    for (unsigned i = 0; i < Props.Props.size(); ++i) {
      expr_vector List(Ctx);
      for (unsigned j = 0; j < Vars.size(); ++j)
        List.push_back(AllRelations[i](Vars[j]) ==
                       Ctx.bool_val(Sets[i].contains(Vars[j])));

      LLVM_DEBUG({
        for (auto const &E : List)
          dbgs() << E.to_string() << ", ";
        dbgs() << "\n";
      });

      Slv.add(List);
    }

    // make mapping for scope args
    std::vector<unsigned> ScopeVars;

    for (unsigned i = 0; i < Scope.size(); ++i) {
      ScopeVars.push_back(i + Vars.size());
      AllNames.push_back(Scope[i]->getName().str());
    }

    for (unsigned i = 0; i < Props.Props.size(); ++i) {
      expr_vector List(Ctx);
      for (unsigned j = 0; j < Scope.size(); ++j)
        List.push_back(AllRelations[i](ScopeVars[j]) ==
                       Ctx.bool_val(Props.Props[i].Set->contains(Scope[j])));
      LLVM_DEBUG({
        for (auto const &E : List)
          dbgs() << E.to_string() << ", ";
        dbgs() << "\n";
      });
      Slv.add(List);
    }

    // product of ScopeVars and CSRVars
    expr_vector Pairs(Ctx);
    std::vector<int> Weights;
    for (auto A : Vars)
      for (auto B : ScopeVars) {
        expr_vector AllRels(Ctx);
        for (auto const &Rel : AllRelations)
          AllRels.push_back(Rel(A) == Rel(B));
        AllRels.push_back(EQUAL[Ctx.int_val(B)] == Ctx.int_val(A));
        Pairs.push_back(mk_and(AllRels));
        Weights.push_back(1);
      }
    LLVM_DEBUG({
      for (auto const &E : Pairs)
        dbgs() << E.to_string() << "\n";
    });

    Slv.add(pbeq(Pairs, Weights.data(), CARE));

    expr s0 = Ctx.int_const("s0");
    expr s1 = Ctx.int_const("s1");
    int LB = ScopeVars.front();
    int UB = ScopeVars.back();
    Slv.add(forall(s0, s1,
                   implies(LB <= s0 && s0 <= UB && LB <= s1 && s1 <= UB &&
                               EQUAL[s0] == EQUAL[s1],
                           s0 == s1)));

    auto Res = Slv.check();
    if (Res == z3::sat) {
      Model = Slv.get_model();
      LLVM_DEBUG({
        dbgs() << Model.to_string() << "\n";
        for (unsigned i = 0; i < CARE; ++i)
          dbgs() << Model.eval(EQUAL[Ctx.int_val(i + Vars.size())]).to_string()
                 << " ";
        dbgs() << "\n";
        for (unsigned i = 0; i < CARE; ++i) {
          dbgs() << "(" << AllNames[i + Vars.size()] << ", "
                 << (i + Vars.size()) << ") -> "
                 << "("
                 << AllNames[Model.eval(EQUAL[Ctx.int_val(i + Vars.size())])
                                 .as_int64()]
                 << ", "
                 << Model.eval(EQUAL[Ctx.int_val(i + Vars.size())]).as_int64()
                 << ")\n";
        }
      });
      LLVM_DEBUG(dbgs() << "[REV] Format Check for " << FormatName
                        << " succeeded\n");
      return true;
    }
    std::stringstream S;
    S << Res;
    LLVM_DEBUG(dbgs() << "[REV] Format Check for " << FormatName
                      << " failed: " << S.str() << "\n");
    return false;
  }

  virtual func_decl makeMatrix() = 0;
  virtual void makeIndexProperties(expr_vector &Properties) = 0;
  virtual expr makeNumberRows() = 0;
  virtual expr makeNumberNonZero() = 0;
  virtual void printSparseMatrix(z3::model &Model) = 0;
  virtual bool checkInductive(func_decl const &Matrix,
                              SmallPtrSet<Value *, 10> &ScopeSet, Value *Y,
                              Value *LiveOut, expr_vector &GemvArgs,
                              Function &F, DominatorTree &DT) = 0;

  bool checkEquality(Value *LiveOut, Function &F, DominatorTree &DT) {

    expr_vector IdxProperties(Ctx);
    makeIndexProperties(IdxProperties);

    SmallPtrSet<Value *, 10> ScopeSet;
    for (auto *V : Scope)
      ScopeSet.insert(V);
    for (unsigned i = 0; i < CARE; ++i)
      ScopeSet.erase(
          Scope[Model.eval(EQUAL[Ctx.int_val(i + Vars.size())]).as_int64()]);
    Value *Y = dyn_cast<GEPOperator>(getLoadStorePointerOperand(LiveOut))
                   ->getPointerOperand();
    ScopeSet.erase(Y);
    if (ScopeSet.size() != 1)
      llvm_unreachable("Not all args were mapped to a storage format.");
    expr_vector GemvArgs(Ctx);
    GemvArgs.push_back(Converter.FromVal(Y));                 // y
    GemvArgs.push_back(Converter.FromVal(*ScopeSet.begin())); // x

    // TODO fix this
    func_decl ReferenceKernel = Kern->makeKernel(Ctx, *Matrix, GemvArgs);

    expr_vector SpMVArgs(Ctx);
    for (auto *V : Scope)
      SpMVArgs.push_back(Converter.FromVal(V));

    std::vector<expr> GemvParams = {Ctx.int_val(0), makeNumberRows() - 1,
                                    Ctx.int_val(0), m};

    // base cases
    bool BaseCase = true;
    std::vector<std::vector<unsigned>> Bases = {
        {1, 1},
        // TODO: do we need to check all of these? maybe we can get around it.
        // figure out why COO loops on other cases.
        //        {1,2},
        //        {2,1},
        //        {2,2}
    };
    for (auto &Base : Bases) {
      Slv.reset();
      Slv.add(IdxProperties);
      Slv.add(makeNumberRows() == Ctx.int_val(Base[0]));
      Slv.add(m == Ctx.int_val(Base[1]));
      Slv.add(ReferenceKernel(GemvParams.size(), GemvParams.data()) !=
              InputKernel(SpMVArgs));
      auto Res = Slv.check();
      if (Res != z3::unsat) {
        BaseCase = false;
        LLVM_DEBUG({
          z3::model BaseModel = Slv.get_model();
          dbgs() << BaseModel.to_string() << "\n-------------------------\n";
          int64_t _n = BaseModel.eval(n).as_int64();
          int64_t _m = BaseModel.eval(m).as_int64();
          int64_t _nnz = BaseModel.eval(makeNumberNonZero()).as_int64();
          dbgs() << "n = " << _n << ", m = " << _m << ", nnz = " << _nnz
                 << "\n";
          printSparseMatrix(BaseModel);
          expr TestVal = (*Matrix)(Ctx.int_val(0), Ctx.int_val(0));
          std::stringstream M;
          M << BaseModel.eval((*Matrix)(Ctx.int_val(0), Ctx.int_val(0)), true)
            << "\n";
          dbgs() << M.str();

          unsigned I;
          for (I = 0; I < _n; ++I) {
            for (unsigned J = 0; J < _m; ++J) {
              dbgs() << BaseModel
                            .eval((*Matrix)(Ctx.int_val(I), Ctx.int_val(J)))
                            .as_int64()
                     << " ";
            }
            dbgs() << "| "
                   << BaseModel
                          .eval(Converter.FromVal(
                              *ScopeSet.begin())[Ctx.int_val(I)])
                          .as_int64();
            if (I == _n / 2)
              dbgs() << " = ";
            else
              dbgs() << "   ";
            dbgs() << " "
                   << BaseModel.eval(Converter.FromVal(Y)[Ctx.int_val(I)])
                          .as_int64()
                   << "\n";
          }
          for (; I < _m; ++I) {
            for (unsigned Pad = 0; Pad < (_m * 2 + 7); ++Pad)
              dbgs() << " ";
            dbgs() << BaseModel.eval(Converter.FromVal(Y)[Ctx.int_val(I)])
                          .as_int64()
                   << "\n";
          }
          dbgs() << "GEMV\tInputKernel\n";
          for (I = 0; I < _m; ++I) {
            dbgs() << BaseModel
                          .eval(ReferenceKernel(
                              GemvParams.size(),
                              GemvParams.data())[Ctx.int_val(I)])
                          .as_int64()
                   << "\t\t";
            dbgs() << BaseModel.eval(InputKernel(SpMVArgs)[Ctx.int_val(I)])
                          .as_int64()
                   << "\n";
          }
        });
        break;
      }
    }

    if (!BaseCase) {
      LLVM_DEBUG(dbgs() << "[REV] BaseCase failed for " << Kern->SparseName
                        << "+" << FormatName << "\n");
      return false;
    }
    return checkInductive(*Matrix, ScopeSet, Y, LiveOut, GemvArgs, F, DT);
  }

  void setKernel(Kernel *K) { Kern = K; }

  void initEqualityChecking() {
    for (unsigned i = 0; i < CARE; ++i)
      NameMap[AllNames[Model.eval(EQUAL[Ctx.int_val(i + Vars.size())])
                           .as_int64()]] = Scope[i];
    // everything below here uses NameMap
    nnz = makeNumberNonZero();
    n = makeNumberRows();

    Matrix = makeMatrix();
  }

  // private:
  std::string FormatName;
  std::vector<unsigned> Vars;
  std::vector<std::string> Names;
  unsigned CARE; // num vars we care about
  MapTy Map;
  std::vector<std::string> AllNames;
  std::vector<SmallSet<unsigned, 5>> Sets;
  Properties &Props;
  z3::expr EQUAL;
  const std::vector<Value *> &Scope;
  z3::context &Ctx;
  z3::solver &Slv;
  MakeZ3 &Converter;
  func_decl InputKernel;
  z3::expr n;
  z3::expr m;
  z3::expr nnz;
  z3::model Model;
  Kernel *Kern = nullptr;
  std::optional<func_decl> Matrix;
  NameMapTy NameMap;
};

class CSRFormat : public Format {
public:
  CSRFormat(Properties &Props, z3::context &Ctx,
            const std::vector<Value *> &Scope, z3::solver &Slv,
            MakeZ3 &Converter, func_decl InputKernel)
      : Format(Props, Ctx, Scope, Slv, Converter, InputKernel) {
    FormatName = "CSR";
    CARE = 4;
    Names.push_back("n");
    Names.push_back("rowPtr");
    Names.push_back("col");
    Names.push_back("val");
    for (unsigned i = 0; i < CARE; ++i) {
      Vars.push_back(i);
      Map[Names[i].c_str()] = Vars[i];
    }
    AllNames.resize(Vars.size());
    for (unsigned i = 0; i < CARE; ++i)
      AllNames[i] = Names[i];

    Sets.resize(Props.Props.size());
    for (unsigned i = 0; i < Props.Props.size(); ++i) {
      auto &P = Props.Props[i];
      if (P.Name == "readonly") {
        Sets[i].insert(Map["rowPtr"]);
        Sets[i].insert(Map["col"]);
        Sets[i].insert(Map["val"]);
      } else if (P.Name == "int") {
        Sets[i].insert(Map["n"]);
      } else if (P.Name == "array") {
        Sets[i].insert(Map["rowPtr"]);
        Sets[i].insert(Map["col"]);
        Sets[i].insert(Map["val"]);
      } else if (P.Name == "as_address") {
        Sets[i].insert(Map["rowPtr"]);
        Sets[i].insert(Map["col"]);
      } else if (P.Name == "direct_access") {
        Sets[i].insert(Map["rowPtr"]);
        Sets[i].insert(Map["col"]);
        Sets[i].insert(Map["val"]);
      } else if (P.Name == "loop_bounds") {
        Sets[i].insert(Map["rowPtr"]);
      }
    }
  }

  func_decl makeMatrix() override {
    expr rptr = Converter.FromVal(NameMap["rowPtr"]);
    expr col = Converter.FromVal(NameMap["col"]);
    expr val = Converter.FromVal(NameMap["val"]);
    expr n = Ctx.int_const("n");
    expr m = Ctx.int_const("m");
    expr t = Ctx.int_const("t");
    expr_vector Args(Ctx);
    Args.push_back(n);
    Args.push_back(m);
    func_decl A = Ctx.recfun("A", Ctx.int_sort(), Ctx.int_sort(),
                             val[Ctx.int_val(0)].get_sort());
    Ctx.recdef(A, Args,
               ite(exists(t, rptr[n] <= t && t < rptr[n + 1] && col[t] == m),
                   Ctx.int_val(1), Ctx.int_val(0)));
    return A;
  }

  void makeIndexProperties(expr_vector &Properties) override {
    assert(Properties.size() == 0);
    expr n = Converter.FromVal(NameMap["n"]);
    expr rptr = Converter.FromVal(NameMap["rowPtr"]);
    expr col = Converter.FromVal(NameMap["col"]);
    expr val = Converter.FromVal(NameMap["val"]);
    expr s = Ctx.int_const("s");
    expr t = Ctx.int_const("t");
    Properties.push_back(nnz > 0);
    // monotonicty
    Properties.push_back(forall(
        s, implies(0 <= s && s <= n, rptr[s] <= rptr[s + 1] && rptr[s] >= 0)));
    // pmonotonicity
    Properties.push_back(
        forall(s, implies(0 <= s && s < n,
                          forall(t, implies(rptr[s] <= t && t < rptr[s + 1],
                                            col[t] < col[t + 1])))));
    // extra constraints
    Properties.push_back(
        forall(s, implies(0 <= s && s < nnz, col[s] >= 0 && col[s] < m)));
    Properties.push_back(forall(s, implies(0 <= s && s < nnz, val[s] == 1)));

    Properties.push_back(rptr[Ctx.int_val(0)] == 0);
    Properties.push_back(rptr[n] == nnz);
    Properties.push_back(nnz <= n * m);
    return;
  }

  expr makeNumberRows() override { return Converter.FromVal(NameMap["n"]); }

  expr makeNumberNonZero() override { return nnz; }

  void printSparseMatrix(z3::model &Model) override {}

  bool checkInductive(func_decl const &Matrix,
                      SmallPtrSet<Value *, 10> &ScopeSet, Value *Y,
                      Value *LiveOut, expr_vector &GemvArgs, Function &F,
                      DominatorTree &DT) override {

    expr_vector IdxProperties(Ctx);
    makeIndexProperties(IdxProperties);

    // inductive step
    Slv.reset();
    expr rptr = Converter.FromVal(NameMap["rowPtr"]);
    expr val = Converter.FromVal(NameMap["val"]);
    Slv.add(IdxProperties);
    Slv.add(n > 2);
    Slv.add(m > 2);

    SmallVector<std::pair<const BasicBlock *, const BasicBlock *>> Cycles;
    FindFunctionBackedges(F, Cycles);
    SSA2Func NoLoopSpMV(Ctx, &DT, &Converter, LiveOut);
    auto StraightLine = NoLoopSpMV.straightlineFromFunction(&F, &Cycles);

    expr DummyRptr = Ctx.constant(
        "DummyRptr", Ctx.array_sort(Ctx.int_sort(), Ctx.int_sort()));
    expr DummyCol = Ctx.constant(
        "DummyCol", Ctx.array_sort(Ctx.int_sort(), Ctx.int_sort()));
    expr DummyVal = Ctx.constant(
        "DummyVal", Ctx.array_sort(Ctx.int_sort(), Ctx.int_sort()));

    // case 1: new elem is zero
    Slv.add(DummyRptr[Ctx.int_val(0)] == nnz);
    Slv.add(DummyRptr[Ctx.int_val(1)] == nnz);
    Slv.add(DummyCol[Ctx.int_val(0)] == 0);
    Slv.add(DummyVal[Ctx.int_val(0)] == 0);
    std::vector<expr> StraightlineArgs = {Converter.FromVal(NameMap["n"]),
                                          DummyRptr,
                                          DummyCol,
                                          DummyVal,
                                          Converter.FromVal(*ScopeSet.begin()),
                                          Converter.FromVal(Y)};
    std::vector<expr> GemvIndParams = {Ctx.int_val(0), makeNumberRows() - 1,
                                       Ctx.int_val(0), m};
    func_decl GemvNoLoop = Kern->makeKernelNoLoop(Ctx, DummyVal, GemvArgs);
    Slv.add(GemvNoLoop(GemvIndParams.size(), GemvIndParams.data()) !=
            StraightLine(StraightlineArgs.size(), StraightlineArgs.data()));
    auto Case1 = Slv.check();
    if (Case1 != z3::unsat) {
      std::stringstream S;
      S << Case1;
      LLVM_DEBUG(dbgs() << "[REV] Case1 failed: " << S.str() << "\n");
      return false;
    }

    Slv.reset(); // Case (2)
    Slv.add(IdxProperties);
    Slv.add(n > 2);
    Slv.add(m > 2);
    Slv.add(DummyRptr[Ctx.int_val(0)] == 0);
    Slv.add(DummyRptr[Ctx.int_val(1)] == 1);
    Slv.add(DummyCol[Ctx.int_val(0)] == 0);
    Slv.add(DummyVal[Ctx.int_val(0)] != 0);
    Slv.add(GemvNoLoop(GemvIndParams.size(), GemvIndParams.data()) !=
            StraightLine(StraightlineArgs.size(), StraightlineArgs.data()));
    auto Case2 = Slv.check();
    if (Case2 != z3::unsat) {
      std::stringstream S;
      S << Case2;
      LLVM_DEBUG(dbgs() << "[REV] Case2 failed: " << S.str() << "\n");
      return false;
    }

    Slv.reset(); // Case (3) new col element
    Slv.add(IdxProperties);
    Slv.add(n > 2);
    Slv.add(m > 2);
    Slv.add(DummyRptr[Ctx.int_val(0)] == 0);
    Slv.add(DummyRptr[Ctx.int_val(1)] == 0);
    //    Slv.add(DummyCol[Ctx.int_val(0)] == m);
    Slv.add(DummyVal[Ctx.int_val(0)] == 0);
    Slv.add(GemvNoLoop(GemvIndParams.size(), GemvIndParams.data()) !=
            StraightLine(StraightlineArgs.size(), StraightlineArgs.data()));
    auto Case3 = Slv.check();
    if (Case3 != z3::unsat) {
      std::stringstream S;
      S << Case3;
      LLVM_DEBUG(dbgs() << "[REV] Case3 failed: " << S.str() << "\n");
      return false;
    }

    Slv.reset(); // Case (4) new col element
    Slv.add(IdxProperties);
    Slv.add(n > 2);
    Slv.add(m > 2);
    Slv.add(DummyRptr[Ctx.int_val(0)] == m);
    Slv.add(DummyRptr[Ctx.int_val(1)] == m + 1);
    Slv.add(DummyCol[m] == m);
    Slv.add(DummyVal[m] != 0);
    std::vector<expr> GemvIndParams2 = {Ctx.int_val(0), Ctx.int_val(1), m,
                                        m + 1};
    Slv.add(GemvNoLoop(GemvIndParams2.size(), GemvIndParams2.data()) !=
            StraightLine(StraightlineArgs.size(), StraightlineArgs.data()));
    auto Case4 = Slv.check();
    if (Case4 != z3::unsat) {
      std::stringstream S;
      S << Case4;
      LLVM_DEBUG(dbgs() << "[REV] Case4 failed: " << S.str() << "\n");
      return false;
    }

    return true;
  }
};

class COOFormat : public Format {
public:
  COOFormat(Properties &Props, z3::context &Ctx,
            const std::vector<Value *> &Scope, z3::solver &Slv,
            MakeZ3 &Converter, func_decl InputKernel)
      : Format(Props, Ctx, Scope, Slv, Converter, InputKernel) {
    FormatName = "COO";
    CARE = 4;
    Names.push_back("nz");
    Names.push_back("rowind");
    Names.push_back("colind");
    Names.push_back("val");
    for (unsigned i = 0; i < CARE; ++i) {
      Vars.push_back(i);
      Map[Names[i].c_str()] = Vars[i];
    }
    AllNames.resize(Vars.size());
    for (unsigned i = 0; i < CARE; ++i)
      AllNames[i] = Names[i];

    Sets.resize(Props.Props.size());
    for (unsigned i = 0; i < Props.Props.size(); ++i) {
      auto &P = Props.Props[i];
      if (P.Name == "readonly") {
        Sets[i].insert(Map["val"]);
        Sets[i].insert(Map["colind"]);
        Sets[i].insert(Map["rowind"]);
      } else if (P.Name == "int") {
        Sets[i].insert(Map["nz"]);
      } else if (P.Name == "array") {
        Sets[i].insert(Map["rowind"]);
        Sets[i].insert(Map["colind"]);
        Sets[i].insert(Map["val"]);
      } else if (P.Name == "as_address") {
        Sets[i].insert(Map["rowind"]);
        Sets[i].insert(Map["colind"]);
      } else if (P.Name == "direct_access") {
        Sets[i].insert(Map["rowind"]);
        Sets[i].insert(Map["colind"]);
        Sets[i].insert(Map["val"]);
      } else if (P.Name == "loop_bounds") {
        //        Sets[i].insert(Map["rowPtr"]);
      }
    }
  }

  func_decl makeMatrix() override {
    expr rowind = Converter.FromVal(NameMap["rowind"]);
    expr colind = Converter.FromVal(NameMap["colind"]);
    expr val = Converter.FromVal(NameMap["val"]);
    expr i = Ctx.int_const("i");
    expr j = Ctx.int_const("j");
    expr t = Ctx.int_const("t");
    expr_vector Args(Ctx);
    Args.push_back(i);
    Args.push_back(j);
    func_decl A = Ctx.recfun("A", Ctx.int_sort(), Ctx.int_sort(),
                             val[Ctx.int_val(0)].get_sort());
    std::vector<z3::sort> SearchSorts = {Ctx.int_sort(), Ctx.int_sort(),
                                         Ctx.int_sort()};
    func_decl Search =
        Ctx.recfun("Search", SearchSorts.size(), SearchSorts.data(),
                   val[Ctx.int_val(0)].get_sort());
    expr_vector SearchArgs(Ctx);
    SearchArgs.push_back(t);
    SearchArgs.push_back(i);
    SearchArgs.push_back(j);
    Ctx.recdef(
        A, Args,
        ite(exists(
                t,
                0 <= t && t < nnz &&
                    rowind[t] == i && colind[t] == j),
            Ctx.int_val(1), Ctx.int_val(0)));

    return A;
  }

  void makeIndexProperties(expr_vector &Properties) override {
    expr nnz = Converter.FromVal(NameMap["nz"]);
    expr rowind = Converter.FromVal(NameMap["rowind"]);
    expr colind = Converter.FromVal(NameMap["colind"]);
    expr val = Converter.FromVal(NameMap["val"]);
    expr s = Ctx.int_const("s");
    expr t = Ctx.int_const("t");

    Properties.push_back(nnz > 0);
    Properties.push_back(nnz <= makeNumberRows() * m);
    //    Properties.push_back(forall(s, implies(0 <= s && s < nnz, val[s] ==
    //    1)));
    Properties.push_back(
        forall(s, implies(0 <= s && s < nnz, 0 <= rowind[s] && rowind[s] < n)));
    Properties.push_back(
        forall(s, implies(0 <= s && s < nnz, 0 <= colind[s] && colind[s] < m)));
    Properties.push_back(forall(s, val[s] == 1));
    // TODO incomplete
  }

  expr makeNumberRows() override { return n; }
  expr makeNumberNonZero() override { return Converter.FromVal(NameMap["nz"]); }

  void printSparseMatrix(z3::model &Model) override {
    int64_t nnz = Model.eval(Converter.FromVal(NameMap["nz"])).as_int64();
    dbgs() << "val\n";
    for (unsigned i = 0; i < nnz; ++i)
      dbgs() << Model.eval(Converter.FromVal(NameMap["val"])[Ctx.int_val(i)])
                    .as_int64()
             << " ";
    dbgs() << "\n";
    dbgs() << "rowind\tcolind\n";
    for (unsigned i = 0; i < nnz; ++i) {
      dbgs() << Model.eval(Converter.FromVal(NameMap["rowind"])[Ctx.int_val(i)])
                    .as_int64()
             << "\t";
      dbgs() << Model.eval(Converter.FromVal(NameMap["colind"])[Ctx.int_val(i)])
                    .as_int64()
             << "\n";
    }
  }

  bool checkInductive(func_decl const &Matrix,
                      SmallPtrSet<Value *, 10> &ScopeSet, Value *Y,
                      Value *LiveOut, expr_vector &GemvArgs, Function &F,
                      DominatorTree &DT) override {

    expr_vector IdxProperties(Ctx);
    makeIndexProperties(IdxProperties);

    // inductive step
    Slv.reset();
    //    expr n = makeNumberRows();
    //    expr nnz = makeNumberNonZero();
    expr rowind = Converter.FromVal(NameMap["rowind"]);
    expr colind = Converter.FromVal(NameMap["colind"]);
    expr val = Converter.FromVal(NameMap["val"]);
    expr t = Ctx.int_const("t");
    Slv.add(IdxProperties);
    Slv.add(n > 2);
    Slv.add(m > 2);

    SmallVector<std::pair<const BasicBlock *, const BasicBlock *>> Cycles;
    FindFunctionBackedges(F, Cycles);
    SSA2Func NoLoopSpMV(Ctx, &DT, &Converter, LiveOut);
    auto StraightLine = NoLoopSpMV.straightlineFromFunction(&F, &Cycles);

    expr DummyRowInd = Ctx.constant("DummyRowInd", rowind.get_sort());
    expr DummyColInd = Ctx.constant("DummyColInd", colind.get_sort());
    expr DummyVal = Ctx.constant("DummyVal", val.get_sort());

    // case 1: new elem is zero
    Slv.add(nnz == 0);
    Slv.add(DummyVal[Ctx.int_val(0)] == 0);
    std::vector<expr> StraightlineArgs = {DummyRowInd,
                                          DummyColInd,
                                          DummyVal,
                                          makeNumberNonZero(),
                                          Converter.FromVal(*ScopeSet.begin()),
                                          Converter.FromVal(Y)};
    std::vector<expr> GemvIndParams = {Ctx.int_val(0), makeNumberRows() - 1,
                                       Ctx.int_val(0), m};
    func_decl GemvNoLoop = Kern->makeKernelNoLoop(Ctx, DummyVal, GemvArgs);
    Slv.add(GemvNoLoop(GemvIndParams.size(), GemvIndParams.data()) !=
            StraightLine(StraightlineArgs.size(), StraightlineArgs.data()));
    auto Case1 = Slv.check();
    if (Case1 != z3::unsat) {
      std::stringstream S;
      S << Case1;
      LLVM_DEBUG(dbgs() << "[REV] Case1 failed: " << S.str() << "\n");
      return false;
    }

    Slv.reset(); // Case (2)
    Slv.add(IdxProperties);
    Slv.add(n > 2);
    Slv.add(m > 2);
    Slv.add(nnz == 1);
    Slv.add(DummyRowInd[Ctx.int_val(0)] == n);
    Slv.add(DummyColInd[Ctx.int_val(0)] == 0);
    Slv.add(DummyVal[Ctx.int_val(0)] != 0);
    Slv.add(DummyVal[n * m] != 0);
    Slv.add(DummyVal[n * m] == DummyVal[Ctx.int_val(0)]);
    std::vector<expr> GemvIndParams2 = {n, n + 1, Ctx.int_val(0), m};
    Slv.add(GemvNoLoop(GemvIndParams2.size(), GemvIndParams2.data()) !=
            StraightLine(StraightlineArgs.size(), StraightlineArgs.data()));
    auto Case2 = Slv.check();
    if (Case2 != z3::unsat) {
      std::stringstream S;
      S << Case2;
      LLVM_DEBUG(dbgs() << "[REV] Case2 failed: " << S.str() << "\n");
      return false;
    }

    // TODO this is the same as case (1)
    Slv.reset(); // Case (3) new col element
    Slv.add(IdxProperties);
    Slv.add(n > 2);
    Slv.add(m > 2);
    Slv.add(nnz == 0);
    //    Slv.add(DummyRowInd[Ctx.int_val(0)] == 0);
    //    Slv.add(DummyColInd[Ctx.int_val(0)] == m);
    //    Slv.add(DummyVal[Ctx.int_val(0)] == 0);
    Slv.add(GemvNoLoop(GemvIndParams.size(), GemvIndParams.data()) !=
            StraightLine(StraightlineArgs.size(), StraightlineArgs.data()));
    auto Case3 = Slv.check();
    if (Case3 != z3::unsat) {
      std::stringstream S;
      S << Case3;
      LLVM_DEBUG(dbgs() << "[REV] Case3 failed: " << S.str() << "\n");
      return false;
    }

    Slv.reset(); // Case (4) new col element
    Slv.add(IdxProperties);
    Slv.add(n > 2);
    Slv.add(m > 2);
    Slv.add(nnz == 1);
    Slv.add(DummyRowInd[Ctx.int_val(0)] == 0);
    Slv.add(DummyColInd[Ctx.int_val(0)] == m);
    Slv.add(DummyVal[Ctx.int_val(0)] != 0);
    Slv.add(DummyVal[m] != 0);
    Slv.add(DummyVal[m] == DummyVal[Ctx.int_val(0)]);
    std::vector<expr> GemvIndParams4 = {Ctx.int_val(0), n - 1, m, m + 1};
    Slv.add(GemvNoLoop(GemvIndParams4.size(), GemvIndParams4.data()) !=
            StraightLine(StraightlineArgs.size(), StraightlineArgs.data()));
    auto Case4 = Slv.check();
    if (Case4 != z3::unsat) {
      std::stringstream S;
      S << Case4;
      LLVM_DEBUG(dbgs() << "[REV] Case4 failed: " << S.str() << "\n");
      return false;
    }

    return true;
  }
};

PreservedAnalyses RevAnalysisPass::run(Function &F,
                                       FunctionAnalysisManager &AM) {
  if (!EnableLifting)
    return PreservedAnalyses::all();

  LLVM_DEBUG(dbgs() << F.getName() << "\n");

  // TODO replace with better legality analysis
  //  if (F.getName() != "spMV_Mul_csr")
  //    return PreservedAnalyses::all();

  auto start = high_resolution_clock::now();

  AssumptionCache AC = AM.getResult<AssumptionAnalysis>(F);
  DominatorTree &DT = AM.getResult<DominatorTreeAnalysis>(F);
  DemandedBits DB(F, AC, DT);
  Module *M = F.getParent();
  LLVMContext &C = M->getContext();

  LoopInfo &LI = AM.getResult<LoopAnalysis>(F);
  ScalarEvolution &SE = AM.getResult<ScalarEvolutionAnalysis>(F);

  if (LI.getTopLevelLoops().size() == 0)
    return PreservedAnalyses::all();

  LoopNest LN(*LI.getTopLevelLoops()[0], SE);

  context Ctx;
  TerminalMap BB2Func(Ctx), Env(Ctx);
  MakeZ3 Converter(Env, SE, Ctx);
  Loop *OuterLoop = &LN.getOutermostLoop();

  SmallPtrSet<Value *, 4> LiveOuts;
  GetLiveOuts(OuterLoop, LiveOuts);
  assert(LiveOuts.size() == 1 && "only 1 output tensor supported for now");
  auto *LiveOut = (*LiveOuts.begin());

  SSA2Func Translate(Ctx, &DT, &Converter, LiveOut);
  Translate.fromFunction(&F);

  solver Slv(Ctx);
  Slv.set("smtlib2_log", "spmv_csr_test_log.smt2");
#ifdef NDEBUG
  Slv.set("timeout", 500u);
#else
  Slv.set("timeout", 2000u);
#endif

  // Goal: match array inputs to storage formats
  // array inputs: some subset of Scopes[header]
  // need to figure out which belong in the storage set or not

  Properties Props(LN, SE);
  auto &Scope = Translate.Scopes[&F.getEntryBlock()];
  Props.buildSets(Scope);
  LLVM_DEBUG({
    for (auto &Prop : Props.Props) {
      dbgs() << Prop.Name << ": ";
      for (auto *V : *Prop.Set)
        dbgs() << *V << " ";
      dbgs() << "\n";
    }
  });

  CSRFormat CSR_F(Props, Ctx, Scope, Slv, Converter,
                  Translate[&F.getEntryBlock()]);
  COOFormat COO_F(Props, Ctx, Scope, Slv, Converter,
                  Translate[&F.getEntryBlock()]);
  bool Res = false;
  Format *ValidFormat = nullptr;
  std::vector<Format *> FormatList = {&CSR_F, &COO_F};
  for (auto *Cur : FormatList) {
    if (Cur->validateMapping()) {
      if (Res)
        llvm_unreachable("[REV] Multiple valid formats!");
      Res = true;
      ValidFormat = Cur;
    }
  }

  if (!Res) {
    LLVM_DEBUG(dbgs() << "[REV] No viable format mappings found\n");
    return PreservedAnalyses::all();
  }

  // Now test every possible kernel

  ValidFormat->initEqualityChecking();

  GEMV MV;
  GEMV_reset MV_reset;
  std::vector<Kernel *> Kernels = {&MV, &MV_reset};

  std::optional<std::pair<Format *, Kernel *>> Result;
  for (auto *K : Kernels) {
    ValidFormat->setKernel(K);
    if (ValidFormat->checkEquality(LiveOut, F, DT)) {
      assert(!Result.has_value() && "Multiple possible formats!");
      Result = {ValidFormat, K};
    }
  }

  if (Result) {
    LLVM_DEBUG({
      dbgs() << "[REV] mapping found\n";
      dbgs() << "Mapping: \n";
      dbgs() << "Input program = " << (*Result).second->Name << "\n";
      dbgs() << "Storage Format = " << (*Result).first->FormatName << "\n";
    });

    // now actually modify the IR

    // cmp1 = @call(my_special_function)
    // br i8 cmp1 (exit block), (entry block)

    BasicBlock *OldEntry = &F.getEntryBlock();
    IRBuilder<> Builder(C);
    BasicBlock *NewEntry =
        BasicBlock::Create(C, "rev.entry", &F, &F.getEntryBlock());
    BasicBlock *NewExit = BasicBlock::Create(C, "rev.exit", &F);
    Builder.SetInsertPoint(NewExit);
    Builder.CreateRetVoid();

    Builder.SetInsertPoint(NewEntry);

    SmallVector<Type *> ArgTypes;
    for (auto *V : Scope)
      ArgTypes.push_back(V->getType());

    auto *FType = FunctionType::get(Type::getInt8Ty(C), ArgTypes, false);
    auto FHandle = F.getParent()->getOrInsertFunction(
        (*Result).second->SparseName + "_" + (*Result).first->FormatName + "_D",
        FType);
    Value *CallResult = Builder.CreateCall(FHandle, Scope, "dsl.call");
    Value *CmpResult = Builder.CreateICmpEQ(
        CallResult, ConstantInt::get(Type::getInt8Ty(C), 1), "rt.check");
    Builder.CreateCondBr(CmpResult, NewExit, OldEntry);

    LLVM_DEBUG(dbgs() << *F.getParent());
    // TODO only abandon the analyses we changed
    return PreservedAnalyses::none();
  }

  LLVM_DEBUG(dbgs() << "[REV] Kernel is not GEMV.\n");

  return PreservedAnalyses::all();
}

// THE MAGIC COMMAND LINE TEXT:
// LD_LIBRARY_PATH=/usr/local/lib ./clang -O3
// -I/opt/intel/oneapi/mkl/latest/include
// -L/opt/intel/oneapi/mkl/latest/lib/intel64 -lmkl_intel_lp64 -lmkl_rt
// -lmkl_sequential -lmkl_core -lm -fopenmp ../../../scripts/spmv_csr.c
// ../../../rev-rt/RevRT.cpp -o spmv_mkl_test.ll