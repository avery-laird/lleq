//
// Created by avery on 27/06/23.
//

#include "llvm/IR/Operator.h"
#include "llvm/Analysis/REVPass.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopNestAnalysis.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Support/YAMLTraits.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/PatternMatch.h"
#include "llvm/IR/Argument.h"
#include "llvm/Support/Debug.h"

#define DEBUG_TYPE "revpass"

using namespace llvm;
using namespace PatternMatch;
using llvm::yaml::Output;
using llvm::yaml::MappingTraits;
using llvm::yaml::IO;

static cl::opt<std::string> AnalysisOutputPath(
    "revpass-output", cl::Hidden,
    cl::desc("The output path for revpass."));

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

//void denseLocateFunctions() {
//
//}

std::string getNameOrAsOperand(Value *V) {
  //  if (!V->getName().empty())
  //    return std::string(V->getName());

  std::string BBName;
  raw_string_ostream OS(BBName);
  V->printAsOperand(OS, false);
  return OS.str();
}


enum LevelTypeEnum {
  COMPRESSED,
  DENSE,
  UNKNOWN
};


struct LevelBounds {
  LevelTypeEnum LevelType;
  PHINode *Iterator = nullptr;
  Value *LowerBound = nullptr;
  Value *UpperBound = nullptr;
  Value *IndexExpr = nullptr;
  Value *BasePtr = nullptr;
};

void findCrd(PHINode *IndVar, Value **Crd) {
  std::vector<Value*> Queue;
  SmallPtrSet<Value*, 4> Visited;
  Queue.push_back(IndVar);
  int LoadCount = 0;
  while (!Queue.empty()) {
    auto *ToVisit = Queue.back();
    Queue.pop_back();
    if (!Visited.contains(ToVisit)) {
      Visited.insert(ToVisit);
      if (auto *Load = dyn_cast<LoadInst>(ToVisit)) {
        if (LoadCount++ == 1)
          return;
        auto *GEP = dyn_cast<GEPOperator>(Load->getPointerOperand());
        *Crd = GEP->getPointerOperand();
      }
      for (auto *Use : ToVisit->users()) {
        Queue.push_back(Use);
      }
    }
  }
  return;
}

void makeLevelBounds(LoopNest *LN, ScalarEvolution *SE, std::vector<LevelBounds> &Levels) {
  DataLayout DL = SE->getDataLayout();
//  PHINode *PrevLevel = nullptr;
  for (auto *Loop : LN->getLoops()) {
    auto Bounds = Loop->getBounds(*SE);
    if (!Bounds.has_value())
      return;
    auto *IndVar = Loop->getInductionVariable(*SE);
    LLVM_DEBUG(dbgs() << getNameOrAsOperand(IndVar) << " = [" << Bounds->getInitialIVValue() << ", " << Bounds->getFinalIVValue() << ") -> \n");

//    std::vector<Value*> Uses;
//    followUses(IndVar, Uses);
//    for (auto *V : Uses) {
//      LLVM_DEBUG(dbgs() << *V << "\n");
//    }

    Value *LowerBound = &Bounds->getInitialIVValue();
    Value *UpperBound = &Bounds->getFinalIVValue();

    bool IsZero = match(LowerBound, m_ZeroInt());
    bool IsInt = isa<ConstantInt>(UpperBound) || isa<Argument>(UpperBound);
    if (IsZero && IsInt) {
      LLVM_DEBUG(dbgs() << "dense\n");
      Levels.push_back({DENSE, IndVar, LowerBound, UpperBound});
//      PrevLevel = IndVar;
      continue ;
    }

    // Detect Compressed Form: pos[i] ==> pos[i+1]
    LoadInst *LowInstr = dyn_cast<LoadInst>(LowerBound);
    LoadInst *UpInstr = dyn_cast<LoadInst>(UpperBound);
    if (LowInstr && UpInstr) {
      Value *LowPtr = getLoadStorePointerOperand(LowInstr);
      Value *UpPtr = getLoadStorePointerOperand(UpInstr);
      auto *LowGEP = dyn_cast<GetElementPtrInst>(LowPtr);
      auto *HighGEP = dyn_cast<GetElementPtrInst>(UpPtr);
      if (LowGEP && HighGEP) {
        Value *LowPtrBase = LowGEP->getPointerOperand();
        Value *HighPtrBase = HighGEP->getPointerOperand();
        const SCEV *LowIndex = SE->getSCEV(LowGEP->getOperand(1));
        Value *IndexExpr = LowGEP->getOperand(1);
        while (auto *PCast = dyn_cast<CastInst>(IndexExpr))
          IndexExpr = PCast->getOperand(0);
        const SCEV *HighIndex = SE->getSCEV(HighGEP->getOperand(1));
        const SCEV *OffsetIndex = SE->getMinusSCEV(HighIndex, LowIndex);
        while (auto *PCast = dyn_cast<CastInst>(LowPtrBase))
          LowPtrBase = PCast->getOperand(0);
        while (auto *PCast = dyn_cast<CastInst>(HighPtrBase))
          HighPtrBase = PCast->getOperand(0);
        bool SameBase = LowPtrBase == HighPtrBase;
        bool OneOffset = OffsetIndex->isOne();
//        bool UsesAncestor = PrevLevel == IndexExpr;
        if (SameBase && OneOffset) {
          LLVM_DEBUG(dbgs() << "sparse\n");
          Levels.push_back({COMPRESSED, IndVar, LowerBound, UpperBound, IndexExpr, LowPtrBase});
//          PrevLevel = IndVar;
          continue;
        }
      }
    }
  }
}

struct CSRLevels {
  LevelBounds I;
  LevelBounds J;
  Value *Pos = nullptr;
  Value *Crd = nullptr;
  Value *Val = nullptr;
};

void findSparseCrd(PHINode *Iterator) {
  // array that is indexed by sparse iterator level
  // and used to index another array
  for (auto *User : Iterator->users()) {
    if (isa<LoadInst>(User)) {

    }
  }
}

bool detectCSR(std::vector<LevelBounds> &Levels, struct CSRLevels *CSR) {
  size_t I, J;
  for (I = 0; I < Levels.size(); ++I) {
    if (Levels[I].LevelType != DENSE)
      continue;
    for (J = I+1; J < Levels.size(); ++J) {
      if (Levels[J].LevelType != COMPRESSED)
        continue;
      if (Levels[J].IndexExpr == nullptr)
        continue;
      if (Levels[J].IndexExpr != Levels[I].Iterator)
        continue;
      CSR->I = Levels[I];
      CSR->J = Levels[J];
      CSR->Pos = Levels[J].BasePtr;
      findCrd(CSR->J.Iterator, &CSR->Crd);
      return true;
    }
  }
  return false;
}

static void GetLiveIns(Function *F, SmallPtrSet<Value *, 4> &LiveIns) {
  for (auto &A : F->args())
    LiveIns.insert(&A);
  return;
}


struct Atom {
  std::string Name;
  std::string Type;
  std::string Pred;
};

std::string Type2String(Value *V) {
  std::string TypeOutput;
  raw_string_ostream TypeOutputStream(TypeOutput);
  V->getType()->print(TypeOutputStream);
  return TypeOutput;
}

struct Node {
  std::string Op;
  std::string Register;
  std::string Type;
  std::vector<Atom> Children;
public:
  Node(Instruction *I) {
    Op = I->getOpcodeName();
    if (auto *ICmp = dyn_cast<ICmpInst>(I)) {
      std::string Pred =
          CmpInst::getPredicateName(ICmp->getPredicate()).str();
      Children.push_back({Pred, "conditioncode"});
    }
    Register = getNameOrAsOperand(I);
    Type = Type2String(I);
    auto *Phi = dyn_cast<PHINode>(I);
    for (auto &C : I->operands()) {
      std::string TypeOutput = Type2String(C);
      std::string Pred = "";
      if (Phi)
        Pred = getNameOrAsOperand(Phi->getIncomingBlock(C));
      Children.push_back({getNameOrAsOperand(C), TypeOutput, Pred});
    }
  }
};

struct BBNode {
  std::string Name;
  std::vector<Node> Nodes;
};

namespace llvm::yaml {

template <> struct MappingTraits<Instruction*> {
  static void mapping(IO &io, Instruction *&I) {
    EmptyContext Ctx;
    yamlize(io, I, false, Ctx);
//    io.mapRequired("op", I->getOpcodeName());
  }
};

template <>
struct SequenceTraits<std::vector<Atom>> {
  static size_t size(IO &io, std::vector<Atom> &list) {
    return list.size();
  }
  static Atom &element(IO &io, std::vector<Atom> &list, size_t index) {
    return list[index];
  }
};

template <>
struct SequenceTraits<std::vector<::Node>> {
  static size_t size(IO &io, std::vector<::Node> &list) {
    return list.size();
  }
  static ::Node &element(IO &io, std::vector<::Node> &list, size_t index) {
    return list[index];
  }
};

template <>
struct SequenceTraits<std::vector<BBNode>> {
  static size_t size(IO &io, std::vector<BBNode> &list) {
    return list.size();
  }
  static BBNode &element(IO &io, std::vector<BBNode> &list, size_t index) {
    return list[index];
  }
};

template <> struct MappingTraits<Atom> {
  static void mapping(IO &io, Atom &A) {
    io.mapRequired("type", A.Type);
    io.mapRequired("name", A.Name);
    if (A.Pred != "")
      io.mapRequired("pred", A.Pred);
  }
};

template <> struct MappingTraits<::Node> {
  static void mapping(IO &io, ::Node &N) {
    io.mapRequired("name", N.Register);
    io.mapRequired("op", N.Op);
    io.mapRequired("type", N.Type);
    io.mapRequired("operands", N.Children);
  }
};

template <> struct MappingTraits<BBNode> {
  static void mapping(IO &io, BBNode &BN) {
    io.mapRequired("name", BN.Name);
    io.mapRequired("nodes", BN.Nodes);
  }
};
} // namespace llvm::yaml


void allLoadsInCurrentScope(Loop *L, SmallPtrSet<LoadInst*, 4> &Loads) {
  for (auto *BB : L->blocks()) {
    for (auto &I : *BB) {
      if (auto *Load = dyn_cast<LoadInst>(&I)) {
        Loads.insert(Load);
      }
    }
  }
}

PreservedAnalyses REVPass::run(Function &F, FunctionAnalysisManager &AM) {
  outs() << F.getName() << "\n";

  LoopInfo &LI = AM.getResult<LoopAnalysis>(F);
  ScalarEvolution &SE = AM.getResult<ScalarEvolutionAnalysis>(F);

  Node *LO;
  std::vector<LevelBounds> Levels;
  struct CSRLevels CSR;
  if (LI.getTopLevelLoops().size() == 0) {
    // TODO handle memory too
    for (auto &BB: F) {
      for (auto &I : BB) {
        if (auto *Ret = dyn_cast<ReturnInst>(&I)) {
          LO = new Node(Ret);
          break; // TODO multiple values
        }
      }
    }
  } else {
    LoopNest LN(*LI.getTopLevelLoops()[0], SE);
    for (int Depth = LN.getNestDepth(); Depth > 0; Depth--) {
      for (auto *Loop : LN.getLoopsAtDepth(Depth)) {
        LLVM_DEBUG(dbgs() << *Loop << "\n");
        SmallPtrSet<LoadInst*, 4> Loads;
        allLoadsInCurrentScope(Loop, Loads);
        for (auto *Load : Loads)
          LLVM_DEBUG(dbgs() << *Load << "\n");
      }
    }

    makeLevelBounds(&LN, &SE, Levels);
//    bool IsCSR = detectCSR(Levels, &CSR);
//    LLVM_DEBUG(dbgs() << "iscsr = " << IsCSR << "\n");

    SmallPtrSet<Value *, 4> LiveOuts;
    GetLiveOuts(&LN.getOutermostLoop(), LiveOuts);

    Instruction *LiveOut = dyn_cast<Instruction>(*LiveOuts.begin());
    LO = new Node(LiveOut);
  }

  std::error_code EC;
  raw_fd_ostream OutputFile(AnalysisOutputPath + ".yaml", EC);
  Output Yout(OutputFile);

  SmallPtrSet<Value *, 4> LiveIns;
  GetLiveIns(&F, LiveIns);
  std::vector<Atom> LiveInList;
  for (auto *LiveIn : LiveIns)
    LiveInList.push_back({getNameOrAsOperand(LiveIn), Type2String(LiveIn), ""});

//  std::vector<Value *> WorkList;
//  WorkList.insert(WorkList.begin(), LiveIns.begin(), LiveIns.end());
//  SmallPtrSet<Value *, 4> Dense;
//  while(!WorkList.empty()) {
//    Value *Head = WorkList.back();
//    if (Head == CSR.I.UpperBound ||
//        Head == CSR.Crd ||
//        Head == CSR.Pos) {
//      WorkList.pop_back();
//    }
//  }

  std::vector<BBNode> AllBBs;
  for (auto &BB : F) {
    BBNode BN;
    BN.Name = BB.getName();
    for (auto &I : BB) {
      BN.Nodes.push_back(Node(&I));
    }
   AllBBs.push_back(BN);
  }
  Yout << AllBBs;
  Yout << *LO;
  Yout << LiveInList;
  return PreservedAnalyses::all();
}