/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticCuspTangent
public import FLT.Mazur.EllipticIntegralSingularTranslation

/-!
# Integral normalization of a cuspidal special fiber

If Δ and c₄ lie in the maximal ideal of a local ring with perfect residue
field, translation and a shear with u=1 put all five Weierstrass coefficients
in that ideal. These are the first coefficient conditions for the additive
branches of the Tate algorithm, without asserting their later valuation tests.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve

variable {R : Type*} [CommRing R] [IsLocalRing R] (W : WeierstrassCurve R)

/-- A residue cusp shear lifts to an integral shear killing all five reduced coefficients. -/
theorem exists_integral_cusp_shear [PerfectField (ResidueField R)]
    (h3 : W.a₃ ∈ maximalIdeal R) (h4 : W.a₄ ∈ maximalIdeal R)
    (h6 : W.a₆ ∈ maximalIdeal R) (hc : W.c₄ ∈ maximalIdeal R) :
    ∃ s : R, let V := VariableChange.mk 1 0 s 0 • W
      V.a₁ ∈ maximalIdeal R ∧ V.a₂ ∈ maximalIdeal R ∧ V.a₃ ∈ maximalIdeal R ∧
        V.a₄ ∈ maximalIdeal R ∧ V.a₆ ∈ maximalIdeal R := by
  have h3' : (W.map (residue R)).a₃ = 0 := (residue_eq_zero_iff _).mpr h3
  have h4' : (W.map (residue R)).a₄ = 0 := (residue_eq_zero_iff _).mpr h4
  have h6' : (W.map (residue R)).a₆ = 0 := (residue_eq_zero_iff _).mpr h6
  have hc' : (W.map (residue R)).c₄ = 0 := by
    rw [map_c₄, residue_eq_zero_iff]
    exact hc
  obtain ⟨s, hs⟩ := exists_normalized_cusp_shear (W.map (residue R)) h3' h4' h6' hc'
  obtain ⟨s, rfl⟩ := residue_surjective s
  have hm : (VariableChange.mk 1 0 s 0 • W).map (residue R) =
      VariableChange.mk 1 0 (residue R s) 0 • W.map (residue R) := by
    rw [← map_variableChange]
    congr 1
  refine ⟨s, ?_⟩
  dsimp only at hs ⊢
  rw [← hm] at hs
  simpa only [WeierstrassCurve.map, residue_eq_zero_iff] using hs

/-- A cuspidal special cubic admits an integral u=1 change with every coefficient
in the maximal ideal, in all residue characteristics. -/
theorem exists_integral_cusp_normalization [PerfectField (ResidueField R)]
    (hΔ : W.Δ ∈ maximalIdeal R) (hc : W.c₄ ∈ maximalIdeal R) :
    ∃ r s t : R, let V := VariableChange.mk 1 r s t • W
      V.a₁ ∈ maximalIdeal R ∧ V.a₂ ∈ maximalIdeal R ∧ V.a₃ ∈ maximalIdeal R ∧
        V.a₄ ∈ maximalIdeal R ∧ V.a₆ ∈ maximalIdeal R := by
  obtain ⟨r, t, h3, h4, h6⟩ := exists_integral_singular_translation W hΔ
  have hc' : (VariableChange.mk 1 r 0 t • W).c₄ ∈ maximalIdeal R := by
    rwa [integral_translation_c₄]
  obtain ⟨s, hs⟩ := exists_integral_cusp_shear _ h3 h4 h6 hc'
  refine ⟨r, s, t, ?_⟩
  dsimp only at hs ⊢
  rw [← mul_smul] at hs
  simpa [VariableChange.mul_def] using hs

end FLT.Mazur
