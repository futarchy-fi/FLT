/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSplitDepthModel
public import FLT.Mazur.EllipticNormalizedTypeII
public import FLT.Mazur.EllipticComponentVariableChange

/-!
# The split multiplicative component quotient at discriminant order one

The depth normalization produces a₆ in m but outside m². The integral
equation then excludes every point reducing to the singular origin. Transport
through the integral coordinate change proves E₀=E and E/E₀ trivial for the
original equation. The point-exclusion lemma is shared with the type II
calculation; no additive reduction is asserted here.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  [PerfectField (ResidueField A)] [(W.map (algebraMap A K)).IsElliptic]
  (hd : W.Δ ∈ maximalIdeal A) (hd' : W.Δ ∉ maximalIdeal A ^ 2)
  (hc : IsUnit W.c₄) (hsplit : (W.nodePoly.map (residue A)).Splits)

include hd hd' hc hsplit

/-- At split discriminant order one every generic point reduces nonsingularly. -/
theorem smoothReduction_of_split_discriminant_order_one
    (P : (W.map (algebraMap A K)).toProjective.Point) : SmoothReduction A W P := by
  classical
  obtain ⟨r, s, t, _, _, h3, h4, h6, h6'⟩ :=
    exists_split_node_discriminant_depth W 1 (by decide) (by simpa using hd) hd' hc hsplit
  let C : VariableChange A := .mk 1 r s t
  have h3' : (C • W).a₃ ∈ maximalIdeal A := Ideal.pow_le_self (by decide : 2 ≠ 0) h3
  have h4' : (C • W).a₄ ∈ maximalIdeal A := Ideal.pow_le_self (by decide : 2 ≠ 0) h4
  have h6'' : (C • W).a₆ ∈ maximalIdeal A := by simpa using h6
  let Q := (integralProjectiveVariableChange A W C).symm P
  have hQ := smoothReduction_of_normalizedTypeII A (C • W) h3' h4' h6'' h6' Q
  have hP := (integralProjectiveVariableChange_smooth A W C Q).mpr hQ
  simpa only [Q, AddEquiv.apply_symm_apply] using hP

/-- Split discriminant order one has no nonidentity rational components. -/
theorem ellipticE0_eq_top_of_split_discriminant_order_one : ellipticE0 A W = ⊤ := by
  apply top_unique
  intro P _
  exact smoothReduction_of_split_discriminant_order_one A W hd hd' hc hsplit P

/-- The actual rational component quotient is trivial at split discriminant order one. -/
theorem ellipticComponent_subsingleton_of_split_discriminant_order_one :
    Subsingleton (EllipticComponentQuotient A W) := by
  have hz (c : EllipticComponentQuotient A W) : c = 0 := by
    obtain ⟨P, rfl⟩ := ellipticComponentHom_surjective A W c
    exact (ellipticComponentHom_eq_zero A W P).mpr
      (smoothReduction_of_split_discriminant_order_one A W hd hd' hc hsplit P)
  exact ⟨fun c d => (hz c).trans (hz d).symm⟩

end FLT.Mazur
