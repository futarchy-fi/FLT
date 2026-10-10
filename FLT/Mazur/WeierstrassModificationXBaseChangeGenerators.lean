/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXBaseChange

/-!
# Original tensor generators under the existing base-change equivalence

The existing equivalence sends pure tensors to the coefficient map times
the new scalar. In particular, the original incidence and slope tensors
become the specialized horizontal generators. These statements do not
identify the later residue normal-form comparison with any replacement map.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.WeierstrassModificationX

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

section BaseChange

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (S : Type*) [CommRing S] [Algebra R S]

/-- The existing base-change equivalence preserves every original pure tensor. -/
theorem baseChangeEquiv_tmul (r : S) (z : Coordinate W s b3 b4 b6) :
    baseChangeEquiv W s b3 b4 b6 S (r ⊗ₜ[R] z) =
      r • coefficientMap W s b3 b4 b6 S z := rfl

/-- The original incidence tensor becomes the actual specialized incidence generator. -/
theorem baseChangeEquiv_t :
    baseChangeEquiv W s b3 b4 b6 S ((1 : S) ⊗ₜ[R] t W s b3 b4 b6) =
      t (W.map (algebraMap R S)) (algebraMap R S s)
        (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6) := by
  rw [baseChangeEquiv_tmul, one_smul, coefficientMap_t]

/-- The original slope tensor becomes the actual specialized slope generator. -/
theorem baseChangeEquiv_v :
    baseChangeEquiv W s b3 b4 b6 S ((1 : S) ⊗ₜ[R] v W s b3 b4 b6) =
      v (W.map (algebraMap R S)) (algebraMap R S s)
        (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6) := by
  rw [baseChangeEquiv_tmul, one_smul, coefficientMap_v]

end BaseChange

end FLT.Mazur.WeierstrassModificationX
