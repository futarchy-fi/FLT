/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticStageCoefficients
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The original residue map on every arithmetic coefficient stage

When π lies in the maximal ideal, each arithmetic thickening retains the
original residue coefficient map. All restrictions induce the same residue
map, and the actual arithmetic smoothing parameter reduces to zero.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonArithmeticStages
open IsLocalRing
variable (A : Type*) [CommRing A] [IsLocalRing A] (π : A)
  (hπ : algebraMap A (ResidueField A) π = 0)

include hπ in
/-- The arithmetic thickening ideal is killed by the original residue morphism. -/
theorem ideal_pow_le_residue_ker (m : ℕ) :
    ideal A π ^ (m + 1) ≤ RingHom.ker (algebraMap A (ResidueField A)) := by
  rw [ideal, Ideal.span_singleton_pow, Ideal.span_le, Set.singleton_subset_iff]
  change algebraMap A (ResidueField A) (π ^ (m + 1)) = 0
  rw [map_pow, hπ, zero_pow (Nat.succ_ne_zero m)]

/-- The actual original residue map factored through the arithmetic thickening. -/
def residueMap (m : ℕ) : Quotient A π m →+* ResidueField A :=
  Ideal.Quotient.lift _ (algebraMap A (ResidueField A)) (ideal_pow_le_residue_ker A π hπ m)

/-- Factoring through a thickening preserves every original integral coefficient. -/
@[simp] theorem residueMap_mk (m : ℕ) (a : A) :
    residueMap A π hπ m (Ideal.Quotient.mk _ a) = algebraMap A (ResidueField A) a := rfl

/-- The actual smoothing parameter vanishes in the original residue field. -/
@[simp] theorem residueMap_parameter (m : ℕ) :
    residueMap A π hπ m (parameter A π m) = 0 := hπ

/-- Every original residue coefficient lifts through each arithmetic stage. -/
theorem residueMap_surjective (m : ℕ) : Function.Surjective (residueMap A π hπ m) := by
  intro x
  obtain ⟨a, ha⟩ := residue_surjective (R := A) x
  exact ⟨Ideal.Quotient.mk _ a, ha⟩

/-- All adjacent arithmetic restrictions retain the same original residue coefficient map. -/
theorem residueMap_restriction (m : ℕ) :
    (residueMap A π hπ m).comp (restriction A π m).toRingHom =
      residueMap A π hπ (m + 1) := by
  apply RingHom.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- Arithmetic specialization followed by residue is the original constant reduction. -/
theorem residueMap_specialization (m : ℕ) :
    (residueMap A π hπ m).comp (specialization A π m).toRingHom =
      (algebraMap A (ResidueField A)).comp
        (PolygonInfinitesimalStages.reduction A m).toRingHom := by
  apply AdjoinRoot.ringHom_ext
  · ext a
    change residueMap A π hπ m (specialization A π m (algebraMap A _ a)) = _
    rw [AlgHom.commutes]
    change algebraMap A (ResidueField A) a =
      algebraMap A (ResidueField A) (PolygonInfinitesimalStages.reduction A m (algebraMap A _ a))
    rw [AlgHom.commutes]
    rfl
  · change residueMap A π hπ m
      (specialization A π m (PolygonInfinitesimalStages.parameter A m)) = _
    rw [specialization_parameter, residueMap_parameter]
    change 0 = algebraMap A (ResidueField A)
      (PolygonInfinitesimalStages.reduction A m (PolygonInfinitesimalStages.parameter A m))
    rw [PolygonInfinitesimalStages.reduction_parameter, map_zero]

end FLT.Mazur.PolygonArithmeticStages
