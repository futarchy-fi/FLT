/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleCoordinateQuotient
public import FLT.GroupScheme.PDivisibleCotangentLimit

/-! # The original cotangent of functions on the coordinate inverse limit -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)

/-- The augmentation of the original coordinate inverse limit. -/
def coordinateAugmentation : X.coordinateLimit →ₐ[R] R :=
  (Bialgebra.counitAlgHom R (X.level 0).CoordinateRing).comp (X.coordinateEval 0)

/-- Every original level computes the same augmentation. -/
theorem coordinateAugmentation_eval (n : ℕ) (x : X.coordinateLimit) :
    Bialgebra.counitAlgHom R (X.level n).CoordinateRing (X.coordinateEval n x) =
      X.coordinateAugmentation x := by
  change _ = Bialgebra.counitAlgHom R (X.level 0).CoordinateRing (X.coordinateEval 0 x)
  rw [← X.coordinateEval_inclusion (Nat.zero_le n) x]
  exact (CoalgHomClass.counit_comp_apply (X.inclusion (Nat.zero_le n)) _).symm

/-- The augmentation ideal of the constructed representing algebra. -/
abbrev coordinateAugmentationIdeal := RingHom.ker X.coordinateAugmentation

/-- Evaluation of functions vanishing at the identity in the original level ideal. -/
def coordinateAugmentationEval (n : ℕ) :
    X.coordinateAugmentationIdeal →ₗ[R] (X.level n).cotangentIdeal :=
  (((X.coordinateEval n).toLinearMap).comp
    (X.coordinateAugmentationIdeal.restrictScalars R).subtype).codRestrict
    ((X.level n).cotangentIdeal.restrictScalars R) (fun x ↦
      (X.coordinateAugmentation_eval n x.val).trans x.property)

/-- Differentiation at the identity with values in the original cotangent limit. -/
def coordinateCotangent : X.coordinateAugmentationIdeal →ₗ[R] X.cotangentLimit :=
  X.cotangentLift
    (fun n ↦ ((X.level n).cotangentIdeal.toCotangent.restrictScalars R).comp
      (X.coordinateAugmentationEval n)) (by
        intro m n h x
        change (X.inclusion h).cotangentMap
          ((X.level n).cotangentIdeal.toCotangent (X.coordinateAugmentationEval n x)) =
          (X.level m).cotangentIdeal.toCotangent (X.coordinateAugmentationEval m x)
        rw [ModelHom.cotangentMap_mk]
        congr 1
        exact Subtype.ext (X.coordinateEval_inclusion h x.val))

/-- The derivative is computed using the original finite cotangent quotient. -/
theorem coordinateCotangent_eval (n : ℕ) (x : X.coordinateAugmentationIdeal) :
    X.cotangentEval n (X.coordinateCotangent x) =
      (X.level n).cotangentIdeal.toCotangent (X.coordinateAugmentationEval n x) := rfl

/-- A function has zero original cotangent precisely when every evaluation is quadratic. -/
theorem coordinateCotangent_eq_zero_iff (x : X.coordinateAugmentationIdeal) :
    X.coordinateCotangent x = 0 ↔
      ∀ n, X.coordinateEval n x.val ∈ (X.level n).cotangentIdeal ^ 2 := by
  constructor
  · intro hx n
    apply (Ideal.toCotangent_eq_zero _ (X.coordinateAugmentationEval n x)).mp
    change X.cotangentEval n (X.coordinateCotangent x) = 0
    rw [hx, map_zero]
  · intro hx
    apply X.cotangentLimit_ext
    intro n
    rw [map_zero, X.coordinateCotangent_eval]
    exact (Ideal.toCotangent_eq_zero _ (X.coordinateAugmentationEval n x)).mpr (hx n)

/-- Original coordinate evaluation is surjective even on the augmentation ideal. -/
theorem coordinateAugmentationEval_surjective (n : ℕ) :
    Function.Surjective (X.coordinateAugmentationEval n) := by
  intro a
  obtain ⟨x, hx⟩ := X.coordinateEval_surjective n a.val
  have hz : X.coordinateAugmentation x = 0 := by
    rw [← X.coordinateAugmentation_eval n x, hx]
    exact a.property
  exact ⟨⟨x, hz⟩, Subtype.ext hx⟩

end ThreeAdicPlan.PDivisibleSystem
