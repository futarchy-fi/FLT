/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealTensorPresentationLift

/-!
# The connecting map from presentation relations to ideal obstructions

An exact presentation with flat middle term gives a canonical linear map
from its reduced kernel to the ideal tensor kernel. Explicit lifts construct
the map; uniqueness proves linearity and independence of the chosen lifts.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.IdealTensorConnectingMap
variable {R P N M : Type*} [CommRing R]
  [AddCommGroup P] [Module R P] [AddCommGroup N] [Module R N]
  [AddCommGroup M] [Module R M]
  (f : P →ₗ[R] N) (q : N →ₗ[R] M)
  (he : Function.Exact f q) (hq : Function.Surjective q) (I : Ideal R)

/-- Choose witnesses for a reduced relation; their resulting ideal obstruction is unique. -/
irreducible_def lifts (z : (f.lTensor (R ⧸ I)).ker) :
    (R ⊗[R] P) × (I ⊗[R] N) :=
  let h := IdealTensorPresentationLift.lift_quotient_kernel f q he hq I z.val z.property
  ⟨h.choose, h.choose_spec.choose⟩

/-- The chosen witnesses satisfy both sides of the tensor presentation square. -/
theorem lifts_spec (z : (f.lTensor (R ⧸ I)).ker) :
    I.mkQ.rTensor P (lifts f q he hq I z).1 = z.val ∧
    I.subtype.rTensor N (lifts f q he hq I z).2 =
      f.lTensor R (lifts f q he hq I z).1 ∧
    I.subtype.rTensor M (q.lTensor I (lifts f q he hq I z).2) = 0 := by
  rw [lifts_def]
  exact (IdealTensorPresentationLift.lift_quotient_kernel
    f q he hq I z.val z.property).choose_spec.choose_spec

variable [Module.Flat R N]
include he hq

/-- Two lifts of the same reduced relation have the same ideal obstruction. -/
theorem lift_independent (u v : R ⊗[R] P) (t s : I ⊗[R] N)
    (hu : f.lTensor R u = I.subtype.rTensor N t)
    (hv : f.lTensor R v = I.subtype.rTensor N s)
    (h : I.mkQ.rTensor P u = I.mkQ.rTensor P v) : q.lTensor I t = q.lTensor I s := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply IdealTensorPresentationLift.ideal_zero_of_quotient_zero f q he hq I
    (t - s) (u - v)
  · simp only [map_sub, hu, hv]
  · rw [map_sub, h, sub_self]

/-- The canonical connecting homomorphism, constructed from actual tensor lifts. -/
def connecting : (f.lTensor (R ⧸ I)).ker →ₗ[R] (I.subtype.rTensor M).ker where
  toFun z := ⟨q.lTensor I (lifts f q he hq I z).2, (lifts_spec f q he hq I z).2.2⟩
  map_add' z w := by
    apply Subtype.ext
    change q.lTensor I (lifts f q he hq I (z + w)).2 =
      q.lTensor I (lifts f q he hq I z).2 + q.lTensor I (lifts f q he hq I w).2
    rw [← map_add]
    apply lift_independent f q he hq I
      (lifts f q he hq I (z + w)).1
      ((lifts f q he hq I z).1 + (lifts f q he hq I w).1)
    · exact (lifts_spec f q he hq I (z + w)).2.1.symm
    · simp only [map_add, ← (lifts_spec f q he hq I z).2.1,
        ← (lifts_spec f q he hq I w).2.1]
    · simp only [map_add, (lifts_spec f q he hq I (z + w)).1,
        (lifts_spec f q he hq I z).1, (lifts_spec f q he hq I w).1]
      rfl
  map_smul' r z := by
    apply Subtype.ext
    change q.lTensor I (lifts f q he hq I (r • z)).2 =
      r • q.lTensor I (lifts f q he hq I z).2
    rw [← map_smul]
    apply lift_independent f q he hq I
      (lifts f q he hq I (r • z)).1 (r • (lifts f q he hq I z).1)
    · exact (lifts_spec f q he hq I (r • z)).2.1.symm
    · simp only [map_smul, ← (lifts_spec f q he hq I z).2.1]
    · simp only [map_smul, (lifts_spec f q he hq I (r • z)).1,
        (lifts_spec f q he hq I z).1]
      rfl

/-- Any pair of compatible lifts computes the same connecting homomorphism. -/
theorem connecting_eq (z : (f.lTensor (R ⧸ I)).ker)
    (u : R ⊗[R] P) (t : I ⊗[R] N)
    (hu : I.mkQ.rTensor P u = z.val) (ht : f.lTensor R u = I.subtype.rTensor N t) :
    (connecting f q he hq I z).val = q.lTensor I t := by
  apply lift_independent f q he hq I (lifts f q he hq I z).1 u
  · exact (lifts_spec f q he hq I z).2.1.symm
  · exact ht
  · exact (lifts_spec f q he hq I z).1.trans hu.symm

end FLT.Mazur.IdealTensorConnectingMap
