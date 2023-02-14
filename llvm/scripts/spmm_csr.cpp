//
// Created by avery on 10/02/23.
//
#include <cstring>

extern "C" {

#define INDPREC int
#define FEATPREC float
#define VALPREC float

INDPREC crbatch;
FEATPREC *currfeat;
FEATPREC *nextfeat;
static INDPREC neuron;
INDPREC *active;
INDPREC **csrdispl;
INDPREC **csrindex;
static VALPREC bias;
VALPREC **csrvalue;

FEATPREC ReLU(FEATPREC x) { return x < 0.0 ? 0.0 : x > 32.0 ? 32.0 : x; };

void spmm_v0(INDPREC l) {
  std::memset(nextfeat, 0, sizeof(FEATPREC) * crbatch * neuron);
  std::memset(active, 0, sizeof(INDPREC) * crbatch);

  for (INDPREC i = 0; i < crbatch; i++) {
    for (INDPREC j = 0; j < neuron; j++) {
      VALPREC result = 0;
      for (INDPREC p = csrdispl[l][j]; p < csrdispl[l][j + 1]; p++) {
        const INDPREC k = csrindex[l][p];
        result += csrvalue[l][p] * currfeat[i * neuron + k];
      }
      nextfeat[i * neuron + j] = ReLU(result + bias);
      if (nextfeat[i * neuron + j])
        active[i] += 1;
    }
  }
}

/** single layer */
void spmm_v1(INDPREC *csr, VALPREC *csrval) {
  std::memset(nextfeat, 0, sizeof(FEATPREC) * crbatch * neuron);
  std::memset(active, 0, sizeof(INDPREC) * crbatch);

  for (INDPREC i = 0; i < crbatch; i++) {
    for (INDPREC j = 0; j < neuron; j++) {
      VALPREC result = 0;
      for (INDPREC p = csr[j]; p < csr[j + 1]; p++) {
        const INDPREC k = csr[p];
        result += csrval[p] * currfeat[i * neuron + k];
      }
      nextfeat[i * neuron + j] = ReLU(result + bias);
      if (nextfeat[i * neuron + j])
        active[i] += 1;
    }
  }
}

/** single layer, single liveout, no relu, no globals */
void spmm_v2(INDPREC *csr, VALPREC *csrval, INDPREC crbatch2, INDPREC neuron2, FEATPREC *currfeat2, FEATPREC *nextfeat2) {
//  std::memset(nextfeat, 0, sizeof(FEATPREC) * crbatch * neuron);
//  std::memset(active, 0, sizeof(INDPREC) * crbatch);

  for (INDPREC i = 0; i < crbatch2; i++) {
    for (INDPREC j = 0; j < neuron2; j++) {
      VALPREC result = 0;
      for (INDPREC p = csr[j]; p < csr[j + 1]; p++) {
        const INDPREC k = csr[p];
        result += csrval[p] * currfeat2[i * neuron2 + k];
      }
      nextfeat2[i * neuron2 + j] = result;
    }
  }
}

}