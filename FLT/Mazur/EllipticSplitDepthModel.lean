/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeDepthNormalization
public import FLT.Mazur.EllipticNodeDiscriminantDepth

/-!
# Split nodal equations at the discriminant depth

The initial split-node normalization and finite-depth translations produce
a₃,a₄ in mⁿ⁺¹ and a₆ of exact depth n when Δ has exact depth n. All changes
are integral with u=1. These are proved coefficient conditions for subsequent
point-valuation calculations, without a supplied component classification.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R] [PerfectField (ResidueField R)]
  (W : WeierstrassCurve R)

/-- A split nodal equation has a finite-depth model with a₆ at exactly the discriminant depth. -/
theorem exists_split_node_discriminant_depth (n : ℕ) (hn : 1 ≤ n)
    (hd : W.Δ ∈ maximalIdeal R ^ n) (hd' : W.Δ ∉ maximalIdeal R ^ (n + 1))
    (hc : IsUnit W.c₄) (hsplit : (W.nodePoly.map (residue R)).Splits) :
    ∃ r s t : R, let V := VariableChange.mk 1 r s t • W
      IsUnit V.a₁ ∧ V.a₂ ∈ maximalIdeal R ∧ V.a₃ ∈ maximalIdeal R ^ (n + 1) ∧
        V.a₄ ∈ maximalIdeal R ^ (n + 1) ∧ V.a₆ ∈ maximalIdeal R ^ n ∧
          V.a₆ ∉ maximalIdeal R ^ (n + 1) := by
  have hd1 : W.Δ ∈ maximalIdeal R := Ideal.pow_le_self (by omega) hd
  obtain ⟨r, s, t, h1, h2, h3, h4, h6⟩ :=
    exists_integral_node_depth_normalization W hd1 hc hsplit n
  have hΔ : (VariableChange.mk 1 r s t • W).Δ = W.Δ := by
    simp [variableChange_Δ]
  exact ⟨r, s, t, h1, h2, h3, h4,
    node_a₆_exact_depth _ h1 h2 h6 n h3 h4 (hΔ ▸ hd) (hΔ ▸ hd')⟩

end FLT.Mazur
