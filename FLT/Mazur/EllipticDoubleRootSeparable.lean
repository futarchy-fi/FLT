/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.DoubleRootComponentBound
public import FLT.Mazur.EllipticDoubleRootCoordinates
public import FLT.Mazur.EllipticTypeIVScaledComparison
public import FLT.Mazur.EllipticTypeIVStarCoordinates

/-!
# The first separable quadratic in the double-root branch

The simple cubic root contributes at most one component. Above the repeated
root, the separable divided y-quadratic contributes at most two opposite
components. Together with zero this bounds the actual quotient by four.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

/-- The first separable y-quadratic terminates the double-root branch with bound four. -/
theorem normalizedDoubleRoot_separable_components {K : Type*} [Field K]
    (A : ValuationSubring K) (W : WeierstrassCurve A) {π : A} (hπ : π ≠ 0)
    (hgen : maximalIdeal A = Ideal.span {π})
    (h1 : W.a₁ ∈ maximalIdeal A) (h2 : W.a₂ ∈ maximalIdeal A)
    (h2' : W.a₂ ∉ maximalIdeal A ^ 2)
    (h3 : W.a₃ ∈ maximalIdeal A ^ 2) (h4 : W.a₄ ∈ maximalIdeal A ^ 3)
    (h6 : W.a₆ ∈ maximalIdeal A ^ 4) (hb6 : W.b₆ ∉ maximalIdeal A ^ 5) :
    Finite (EllipticComponentQuotient A W) ∧ Nat.card (EllipticComponentQuotient A W) ≤ 4 := by
  classical
  obtain ⟨e1, he1⟩ := exists_node_coordinate_factor hgen 1 (by simpa using h1)
  obtain ⟨e2, he2⟩ := exists_node_coordinate_factor hgen 1 (by simpa using h2)
  obtain ⟨e3, he3⟩ := exists_node_coordinate_factor hgen 2 h3
  obtain ⟨e4, he4m, he4⟩ := exists_node_deep_factor hgen 2 h4
  obtain ⟨e6, he6⟩ := exists_node_coordinate_factor hgen 4 h6
  simp only [pow_one] at he1 he2
  have hπm : π ∈ maximalIdeal A := hgen ▸ Ideal.mem_span_singleton_self π
  have he2m : e2 ∉ maximalIdeal A := by
    intro hm
    apply h2'
    rw [he2, pow_two]
    exact Ideal.mul_mem_mul hπm hm
  have h6m := Ideal.pow_le_self (by decide : 4 ≠ 0) h6
  have he6' : W.a₆ = π ^ 3 * (π * e6) := by rw [he6]; ring
  have he6m : π * e6 ∈ maximalIdeal A := (maximalIdeal A).mul_mem_right _ hπm
  let G := EllipticComponentQuotient A W
  let S : G → Prop := fun c => ∃ P, ∃ v : StarZeroCoordinates A W π P,
    residue A v.x = -residue A e2 ∧ ellipticComponentHom A W P = c
  let D : G → Prop := fun c => ∃ P, ∃ _v : TypeIVCoordinates A W (π ^ 2) P,
    ellipticComponentHom A W P = c
  apply finite_card_le_four_of_simple_or_opposite S D
  · intro c hc
    obtain ⟨P, rfl⟩ := ellipticComponentHom_surjective A W c
    obtain ⟨v⟩ := exists_starZeroCoordinates A W hπ hgen e3 e4 (π * e6)
      h1 h2 he3 he4 he6' P (fun hs => hc ((ellipticComponentHom_eq_zero A W P).mpr hs))
    rcases v.doubleRoot_label hπ hπm e2 e3 e4 (π * e6) h1 he2 he3 he4 he6'
        he4m he6m with hx | hx
    · obtain ⟨w⟩ := v.exists_doubleRootCoordinates hgen hx
      exact Or.inr ⟨P, w, rfl⟩
    · exact Or.inl ⟨P, v, hx, rfl⟩
  · rintro c d ⟨P, v, hv, rfl⟩ ⟨Q, w, hw, rfl⟩
    exact v.component_eq_of_doubleRoot_other w hπ hπm e1 e2 e3 e4
      he1 he2 he3 he4 h6m he2m he4m hv hw
  · rintro c d ⟨P, v, rfl⟩ ⟨Q, w, rfl⟩
    exact v.component_eq_or_neg_of_residue_discr w (pow_ne_zero 2 hπ)
      (Ideal.pow_le_self (by decide : 2 ≠ 0) (Ideal.pow_mem_pow hπm 2))
      e3 e4 e6 h1 h2 he4m he3 he4 (by simpa only [← pow_mul] using he6)
      (typeIVStar_residue_discriminant_ne_zero W hπm e3 e6 he3 he6 hb6)

end FLT.Mazur
