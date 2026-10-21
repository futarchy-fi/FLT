/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatInvariantBoundaryMultiplier

/-!
# Original boundary multipliers from full branch coefficient coordinates

The numerator is an actual element of the branch source ring. Independent
endpoint and boundary squares transport its equations through the supplied
full coefficient comparisons. No original representative is required.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.FlatInvariantBoundaryMultiplier
open RingPairInvariantFlatScalars FlatAlgebraEqualizer
variable {A C B : Type*} [CommRing A] [CommRing C] [CommRing B]
  (p q : A →+* C)
local notation "R" => invariants p q
attribute [local instance] sourceAlgebra targetAlgebra
variable [Algebra (invariants p q) B] (f : A →ₐ[invariants p q] B)
  (S : Type*) [CommRing S] [Algebra (invariants p q) S]
  [Module.Flat (invariants p q) S]
  {A' C' B' : Type*} [CommRing A'] [CommRing C'] [CommRing B']
  (ea : S ⊗[invariants p q] A ≃+* A')
  (ec : S ⊗[invariants p q] C ≃+* C')
  (eb : S ⊗[invariants p q] B ≃+* B')
  (p' q' : A' →+* C') (f' : A' →+* B')
  (hp : ∀ x, ec (tensorMap S (first p q) x) = p' (ea x))
  (hq : ∀ x, ec (tensorMap S (second p q) x) = q' (ea x))
  (hf : ∀ x, eb (tensorMap S f x) = f' (ea x))

include hp hq hf in
/-- Full branch equations construct an original multiplier outside the contracted test ideal. -/
theorem exists_original_multiplier_of_coordinates (P : Ideal S) (t : B)
    (s : S) (hs : s ∉ P) (a : A') (he : p' a = q' a)
    (hb : f' a = eb (algebraMap S (S ⊗[R] B) s) * eb (1 ⊗ₜ[R] t)) :
    ∃ r : R, algebraMap R S r ∉ P ∧ ∃ w : R, f w.val = f r.val * t := by
  apply exists_original_multiplier p q f S P t s hs (ea.symm a)
  · apply ec.injective
    rw [hp, hq, ea.apply_symm_apply, he]
  · apply eb.injective
    rw [hf, ea.apply_symm_apply, map_mul, hb]

include hp hq hf in
/-- An unscaled branch lift needs only a proper test ideal, with no chosen branch multiplier. -/
theorem exists_original_multiplier_of_coordinate_lift (P : Ideal S) (hP : P ≠ ⊤)
    (t : B) (a : A') (he : p' a = q' a) (hb : f' a = eb (1 ⊗ₜ[R] t)) :
    ∃ r : R, algebraMap R S r ∉ P ∧ ∃ w : R, f w.val = f r.val * t := by
  apply exists_original_multiplier_of_coordinates p q f S ea ec eb p' q' f' hp hq hf
    P t 1 (fun h ↦ hP (P.eq_top_iff_one.mpr h)) a he
  simpa only [map_one, one_mul] using hb

end FLT.Mazur.FlatInvariantBoundaryMultiplier
