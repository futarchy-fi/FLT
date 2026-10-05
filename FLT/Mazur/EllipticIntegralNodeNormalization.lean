/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeTangent
public import FLT.Mazur.EllipticIntegralSingularTranslation

/-!
# Integral normalization of a split nodal special fiber

A singular special cubic with invertible c₄ and split node polynomial can
be translated and sheared integrally so that a₁ is a unit and a₂,a₃,a₄,a₆
lie in the maximal ideal. This proves the starting normal form for the split
multiplicative calculation without assuming a component-group order.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve

variable {R : Type*} [CommRing R] [IsLocalRing R] (W : WeierstrassCurve R)

/-- Lift a rational nodal tangent slope to an integral shear. -/
theorem exists_integral_node_shear
    (h3 : W.a₃ ∈ maximalIdeal R) (h4 : W.a₄ ∈ maximalIdeal R)
    (h6 : W.a₆ ∈ maximalIdeal R) (hc : IsUnit W.c₄)
    (hsplit : (W.nodePoly.map (residue R)).Splits) :
    ∃ s : R, let V := VariableChange.mk 1 0 s 0 • W
      IsUnit V.a₁ ∧ V.a₂ ∈ maximalIdeal R ∧ V.a₃ ∈ maximalIdeal R ∧
        V.a₄ ∈ maximalIdeal R ∧ V.a₆ ∈ maximalIdeal R := by
  have h3' : (W.map (residue R)).a₃ = 0 := (residue_eq_zero_iff _).mpr h3
  have h4' : (W.map (residue R)).a₄ = 0 := (residue_eq_zero_iff _).mpr h4
  have h6' : (W.map (residue R)).a₆ = 0 := (residue_eq_zero_iff _).mpr h6
  have hc' : (W.map (residue R)).c₄ ≠ 0 := by
    rw [map_c₄, residue_ne_zero_iff_isUnit]
    exact hc
  have hs' : (W.map (residue R)).nodePoly.Splits := by
    rwa [map_nodePoly]
  obtain ⟨s, hs⟩ := exists_normalized_node_shear (W.map (residue R)) h3' h4' h6' hc' hs'
  obtain ⟨s, rfl⟩ := residue_surjective s
  have hm : (VariableChange.mk 1 0 s 0 • W).map (residue R) =
      VariableChange.mk 1 0 (residue R s) 0 • W.map (residue R) := by
    rw [← map_variableChange]
    congr 1
  refine ⟨s, ?_⟩
  dsimp only at hs ⊢
  rw [← hm] at hs
  simpa only [WeierstrassCurve.map, residue_eq_zero_iff, residue_ne_zero_iff_isUnit] using hs

/-- A split nodal special cubic admits the initial integral multiplicative normal form. -/
theorem exists_integral_node_normalization [PerfectField (ResidueField R)]
    (hΔ : W.Δ ∈ maximalIdeal R) (hc : IsUnit W.c₄)
    (hsplit : (W.nodePoly.map (residue R)).Splits) :
    ∃ r s t : R, let V := VariableChange.mk 1 r s t • W
      IsUnit V.a₁ ∧ V.a₂ ∈ maximalIdeal R ∧ V.a₃ ∈ maximalIdeal R ∧
        V.a₄ ∈ maximalIdeal R ∧ V.a₆ ∈ maximalIdeal R := by
  obtain ⟨r, t, h3, h4, h6⟩ := exists_integral_singular_translation W hΔ
  have hc' : IsUnit (VariableChange.mk 1 r 0 t • W).c₄ := by
    rwa [integral_translation_c₄]
  have hs' : ((VariableChange.mk 1 r 0 t • W).nodePoly.map (residue R)).Splits :=
    (nodePoly_map_splits_smul_iff (residue R) W _).mpr hsplit
  obtain ⟨s, hs⟩ := exists_integral_node_shear _ h3 h4 h6 hc' hs'
  refine ⟨r, s, t, ?_⟩
  dsimp only at hs ⊢
  rw [← mul_smul] at hs
  simpa [VariableChange.mul_def] using hs

end FLT.Mazur
