// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.


// Focused adapter derived from upstream verify_test.cc.
#include <iostream>
#include "circuits/ecdsa/verify_circuit.h"
#include "circuits/ecdsa/verify_witness.h"
#include "circuits/logic/evaluation_backend.h"
#include "circuits/logic/logic.h"
#include "ec/p256.h"
using namespace proofs;
struct ecdsa_testvec { StaticString pk_x, pk_y, e, r, s; };
template <class EC, class ScalarField>
bool test_signature3(const struct ecdsa_testvec tests[], size_t num,
                     const EC& ec, const ScalarField& Fn,
                     const typename EC::Field::N& order) {
  using Field = typename EC::Field;
  using EvalBackend = EvaluationBackend<Field>;
  using Logic = Logic<Field, EvalBackend>;

  const Field& F = ec.f_;
  const EvalBackend ebk(F, false);
  const Logic l(&ebk, F);

  using Nat = typename Field::N;
  using Elt = typename Field::Elt;
  using Verc = VerifyCircuit<Logic, Field, EC>;
  using Verw = VerifyWitness3<EC, ScalarField>;

  Verc verc(l, ec, order);

  for (size_t i = 0; i < num; ++i) {
    Elt pk_x = F.of_string(tests[i].pk_x);
    Elt pk_y = F.of_string(tests[i].pk_y);
    Nat e = Nat(tests[i].e);
    Nat r = Nat(tests[i].r);
    Nat s = Nat(tests[i].s);

    Verw vw(Fn, ec);
    vw.compute_witness(pk_x, pk_y, e, r, s);

    typename Verc::Witness vwc;
    vwc.rx = l.konst(vw.rx_);
    vwc.ry = l.konst(vw.ry_);
    vwc.rx_inv = l.konst(vw.rx_inv_);
    vwc.s_inv = l.konst(vw.s_inv_);
    vwc.pk_inv = l.konst(vw.pk_inv_);
    for (size_t j = 0; j < 8; ++j) {
      vwc.pre[j] = l.konst(vw.pre_[j]);
    }
    for (size_t j = 0; j < ec.kBits; j++) {
      vwc.bi[j] = l.konst(vw.bi_[j]);
      if (j < ec.kBits - 1) {
        vwc.int_x[j] = l.konst(vw.int_x_[j]);
        vwc.int_y[j] = l.konst(vw.int_y_[j]);
        vwc.int_z[j] = l.konst(vw.int_z_[j]);
      }
    }

    verc.verify_signature3(l.konst(pk_x), l.konst(pk_y),
                           l.konst(F.to_montgomery(e)), vwc);
    return !ebk.assertion_failed();
  }
  return false;
}

