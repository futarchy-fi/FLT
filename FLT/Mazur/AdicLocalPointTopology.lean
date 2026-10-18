/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicCompleteAffinePoints
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# A common affine neighborhood for a local adic tower

Adjacent compatible maps have the same closed image. Every stage lies in any
open neighborhood of that image, even when the target is not separated.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry IsLocalRing
namespace FLT.Mazur.AdicLocalPointTopology
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R] (I : Ideal R) (hI : I ≠ ⊤)

include hI in
/-- Positive quotients by a proper ideal of a local ring are local. -/
theorem stageLocal (m : ℕ) : IsLocalRing (R ⧸ I ^ (m + 1)) := by
  have hp : I ^ (m + 1) ≠ ⊤ := by
    intro he
    exact (Ideal.pow_eq_top_iff.mp he).elim hI (Nat.succ_ne_zero m)
  let _ : Nontrivial (R ⧸ I ^ (m + 1)) := Ideal.Quotient.nontrivial_iff.mpr hp
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/-- The closed point of the actual positive quotient. -/
def stageClosed (m : ℕ) : Spec (.of (R ⧸ I ^ (m + 1))) :=
  let _ := stageLocal I hI m
  closedPoint (R ⧸ I ^ (m + 1))

/-- Quotient restriction retains the closed point of the original local base. -/
theorem quotient_closed (m : ℕ) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (m + 1))))
      (stageClosed I hI m) = closedPoint R := by
  let _ := stageLocal I hI m
  let _ := IsLocalHom.of_surjective (Ideal.Quotient.mk (I ^ (m + 1)))
    Ideal.Quotient.mk_surjective
  exact Spec_closedPoint

/-- Adjacent restrictions retain the closed points of both actual quotients. -/
theorem transition_closed (m : ℕ) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.le_succ (m + 1)))))
      (stageClosed I hI m) = stageClosed I hI (m + 1) := by
  let _ := stageLocal I hI m
  let _ := stageLocal I hI (m + 1)
  let φ : (R ⧸ I ^ (m + 2)) →+* R ⧸ I ^ (m + 1) :=
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (m + 1)))
  let _ := IsLocalHom.of_surjective φ (Ideal.Quotient.factor_surjective _)
  exact Spec_closedPoint

variable {X : Scheme.{u}}

/-- An open neighborhood of the closed image contains a whole local-base map. -/
theorem range_subset {A : Type u} [CommRing A] [IsLocalRing A]
    (f : Spec (.of A) ⟶ X) (U : X.Opens) (hf : f (closedPoint A) ∈ U) :
    Set.range f ⊆ (U : Set X) := by
  rintro _ ⟨x, rfl⟩
  exact ((specializes_closedPoint x).map f.continuous).mem_open U.isOpen hf

variable (f : ∀ m : ℕ, Spec (.of (R ⧸ I ^ (m + 1))) ⟶ X)
  (hf : ∀ m : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
    (S := I ^ (m + 2)) (T := I ^ (m + 1))
    (Ideal.pow_le_pow_right (Nat.le_succ (m + 1))))) ≫ f (m + 1) = f m)

include hf in
/-- Compatibility identifies all closed images with that of the prescribed first stage. -/
theorem closed_image (m : ℕ) :
    f m (stageClosed I hI m) = f 0 (stageClosed I hI 0) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [← transition_closed I hI m]
    change (Spec.map _ ≫ f (m + 1)) (stageClosed I hI m) = _
    rw [hf, ih]

include hI hf in
/-- A single affine neighborhood contains every map of the actual adic tower. -/
theorem exists_affine : ∃ U : X.Opens, IsAffineOpen U ∧
    ∀ m : ℕ, Set.range (f m) ⊆ (U : Set X) := by
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (U := ⊤) (x := f 0 (stageClosed I hI 0)) trivial
  refine ⟨U, hU, fun m ↦ ?_⟩
  let _ := stageLocal I hI m
  apply range_subset (f m) U
  change f m (stageClosed I hI m) ∈ U
  rw [closed_image I hI f hf]
  exact hx

end FLT.Mazur.AdicLocalPointTopology
