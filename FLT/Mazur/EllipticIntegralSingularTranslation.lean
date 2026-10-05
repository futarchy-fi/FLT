/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticRationalSingularity
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Integral translation of a singular special fiber

Over a local ring with perfect residue field, a discriminant in the maximal
ideal admits an integral translation placing the special singularity at the
origin. Its new a₃,a₄,a₆ lie in the maximal ideal. The translation has u=1
and preserves the discriminant and c₄ exactly.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve

variable {R : Type*} [CommRing R] [IsLocalRing R] (W : WeierstrassCurve R)

/-- Reducing an integral translation translates by the reduced coordinates. -/
theorem map_integral_translation (r t : R) :
    (VariableChange.mk 1 r 0 t • W).map (residue R) =
      VariableChange.mk 1 (residue R r) 0 (residue R t) • W.map (residue R) := by
  rw [← map_variableChange]
  congr 1

omit [IsLocalRing R] in
/-- Integral translations preserve the discriminant exactly. -/
theorem integral_translation_discriminant (r t : R) :
    (VariableChange.mk 1 r 0 t • W).Δ = W.Δ := by
  simp [variableChange_Δ]

omit [IsLocalRing R] in
/-- Integral translations preserve c₄ exactly. -/
theorem integral_translation_c₄ (r t : R) :
    (VariableChange.mk 1 r 0 t • W).c₄ = W.c₄ := by
  simp [variableChange_c₄]

/-- Lifts of a singular residue point give the three normalized coefficient conditions. -/
theorem integral_translation_coefficients {r t : R}
    (he : (W.map (residue R)).toAffine.Equation (residue R r) (residue R t))
    (hn : ¬ (W.map (residue R)).toAffine.Nonsingular (residue R r) (residue R t)) :
    let V := VariableChange.mk 1 r 0 t • W
    V.a₃ ∈ maximalIdeal R ∧ V.a₄ ∈ maximalIdeal R ∧ V.a₆ ∈ maximalIdeal R := by
  have h := translated_singular_coefficients (W.map (residue R)) he hn
  dsimp only at h ⊢
  rw [← map_integral_translation W r t] at h
  simpa only [WeierstrassCurve.map, residue_eq_zero_iff] using h

/-- Every singular special Weierstrass cubic over a perfect residue field can be
normalized by an integral translation with unit coefficient one. -/
theorem exists_integral_singular_translation [PerfectField (ResidueField R)]
    (hΔ : W.Δ ∈ maximalIdeal R) :
    ∃ r t : R, let V := VariableChange.mk 1 r 0 t • W
      V.a₃ ∈ maximalIdeal R ∧ V.a₄ ∈ maximalIdeal R ∧ V.a₆ ∈ maximalIdeal R := by
  have hd : (W.map (residue R)).Δ = 0 := by
    rw [map_Δ, residue_eq_zero_iff]
    exact hΔ
  obtain ⟨x, y, he, hn⟩ := exists_singular_of_discriminant_zero (W.map (residue R)) hd
  obtain ⟨r, rfl⟩ := residue_surjective x
  obtain ⟨t, rfl⟩ := residue_surjective y
  exact ⟨r, t, integral_translation_coefficients W he hn⟩

end FLT.Mazur
