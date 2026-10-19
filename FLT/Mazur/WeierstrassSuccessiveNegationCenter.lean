/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationNegation
public import FLT.Mazur.WeierstrassSuccessiveXReesChart

/-!
# The actual next modification center is invariant under negation

The preceding divided coefficient is the next scale times its actual quotient.
Consequently the full center ideal, including its scheme structure, is fixed by
the constructed divided inverse. This supplies the center input for its next lift.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassDilatation
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
local notation "B" => WeierstrassDilatation.Coordinate W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "X" => WeierstrassDilatation.x W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "Y" => WeierstrassDilatation.y W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "I" => modificationCenter W s π b3 b4 b6
local notation "N" => negation W s (π * b3) (π * b4) (π ^ 2 * b6)

/-- Every original center generator remains in the exact same ideal under negation. -/
theorem modificationCenter_negation_le : (I).map (N).toRingHom ≤ I := by
  rw [Ideal.map_le_iff_le_comap]
  apply Ideal.span_le.mpr
  intro z hz
  rcases hz with rfl | rfl | hz
  · change N (algebraMap R B π) ∈ I
    rw [AlgHom.commutes]
    exact Ideal.subset_span (by simp)
  · change N X ∈ I
    rw [negation_x]
    exact Ideal.subset_span (by simp)
  · obtain rfl := Set.mem_singleton_iff.mp hz
    change N Y ∈ I
    rw [negation_y, map_mul]
    exact (I).sub_mem
      ((I).sub_mem ((I).neg_mem (Ideal.subset_span (by simp)))
        ((I).mul_mem_left _ (Ideal.subset_span (by simp))))
      ((I).mul_mem_right _ (Ideal.subset_span (by simp)))

/-- Negation preserves the full next blowup center, not just its underlying closed points. -/
theorem modificationCenter_negation : (I).map (N).toRingHom = I := by
  have hi : ((I).map (N).toRingHom).map (N).toRingHom = I := by
    rw [Ideal.map_map]
    change (I).map ((N).comp N).toRingHom = I
    rw [negation_comp]
    exact Ideal.map_id I
  apply le_antisymm (modificationCenter_negation_le W s π b3 b4 b6)
  calc
    I = ((I).map (N).toRingHom).map (N).toRingHom := hi.symm
    _ ≤ (I).map (N).toRingHom :=
      Ideal.map_mono (modificationCenter_negation_le W s π b3 b4 b6)

end FLT.Mazur.WeierstrassSuccessiveX
