/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticDoubleRootIteration
public import FLT.Mazur.EllipticTypeIVScaledComparison
public import FLT.Mazur.DoubleRootComponentBound

/-!
# Termination at an odd double-root stage

Exact depth k+2 of a₃ makes the odd y-quadratic separable when a₆ is zero.
The original simple-root class and the two possible deep classes bound the
actual component quotient by four at every such stage.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)

/-- Components represented over the original simple root of the double-root cubic. -/
def DoubleRootSimpleClass (π e2 : A) (c : EllipticComponentQuotient A W) : Prop :=
  ∃ P, ∃ v : StarZeroCoordinates A W π P,
    residue A v.x = -residue A e2 ∧ ellipticComponentHom A W P = c

/-- The original simple-root chart contributes at most one component. -/
theorem doubleRootSimpleClass_unique {π : A} (hπ : π ≠ 0)
    (hgen : maximalIdeal A = Ideal.span {π}) (e2 : A)
    (h1 : W.a₁ ∈ maximalIdeal A) (h2 : W.a₂ = π * e2) (h2m : e2 ∉ maximalIdeal A)
    (h3 : W.a₃ ∈ maximalIdeal A ^ 2) (h4 : W.a₄ ∈ maximalIdeal A ^ 3)
    (h6 : W.a₆ = 0) (c d : EllipticComponentQuotient A W)
    (hc : DoubleRootSimpleClass A W π e2 c) (hd : DoubleRootSimpleClass A W π e2 d) :
    c = d := by
  obtain ⟨e1, he1⟩ := exists_node_coordinate_factor hgen 1 (by simpa using h1)
  obtain ⟨e3, he3⟩ := exists_node_coordinate_factor hgen 2 h3
  obtain ⟨e4, he4m, he4⟩ := exists_node_deep_factor hgen 2 h4
  obtain ⟨P, v, hv, rfl⟩ := hc
  obtain ⟨Q, w, hw, rfl⟩ := hd
  exact v.component_eq_of_doubleRoot_other w hπ (hgen ▸ Ideal.mem_span_singleton_self π)
    e1 e2 e3 e4 (by simpa using he1) h2 he3 he4 (by simp [h6]) h2m he4m hv hw

/-- Exact depth of a₃ terminates any odd double-root stage with bound four. -/
theorem normalizedDoubleRoot_odd_components {π : A} (hπ : π ≠ 0)
    (hgen : maximalIdeal A = Ideal.span {π}) (e2 : A)
    (h1 : W.a₁ ∈ maximalIdeal A) (h2 : W.a₂ = π * e2) (h2m : e2 ∉ maximalIdeal A)
    (k : ℕ) (h3 : W.a₃ ∈ maximalIdeal A ^ (k + 2))
    (h3' : W.a₃ ∉ maximalIdeal A ^ (k + 3))
    (h4 : W.a₄ ∈ maximalIdeal A ^ (k + 3)) (h6 : W.a₆ = 0) :
    Finite (EllipticComponentQuotient A W) ∧ Nat.card (EllipticComponentQuotient A W) ≤ 4 := by
  classical
  obtain ⟨e3, he3⟩ := exists_node_coordinate_factor hgen (k + 2) h3
  obtain ⟨e4, he4m, he4⟩ := exists_node_deep_factor hgen (k + 2) h4
  have hπm : π ∈ maximalIdeal A := hgen ▸ Ideal.mem_span_singleton_self π
  have he3m : residue A e3 ≠ 0 := by
    intro hz
    apply h3'
    rw [he3, pow_succ]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hπm (k + 2)) ((residue_eq_zero_iff _).mp hz)
  let D : EllipticComponentQuotient A W → Prop := fun c =>
    ∃ P, ∃ _v : TypeIVCoordinates A W (π ^ (k + 2)) P, ellipticComponentHom A W P = c
  apply finite_card_le_four_of_simple_or_opposite (DoubleRootSimpleClass A W π e2) D
  · intro c hc
    obtain ⟨P, rfl⟩ := ellipticComponentHom_surjective A W c
    rcases doubleRoot_simple_or_deep_coordinates A W hπ hgen e2 h1 h2 h2m k h3 h4 h6 P
        (fun hs => hc ((ellipticComponentHom_eq_zero A W P).mpr hs)) with hs | hv
    · obtain ⟨v, hv⟩ := hs
      exact Or.inl ⟨P, v, hv, rfl⟩
    · obtain ⟨v⟩ := hv
      exact Or.inr ⟨P, v, rfl⟩
  · exact doubleRootSimpleClass_unique A W hπ hgen e2 h1 h2 h2m
      (Ideal.pow_le_pow_right (by omega) h3) (Ideal.pow_le_pow_right (by omega) h4) h6
  · rintro c d ⟨P, v, rfl⟩ ⟨Q, w, rfl⟩
    apply v.component_eq_or_neg_of_residue_discr w (pow_ne_zero (k + 2) hπ)
      (Ideal.pow_le_self (by omega : k + 2 ≠ 0) (Ideal.pow_mem_pow hπm (k + 2)))
      e3 e4 0 h1 (h2 ▸ (maximalIdeal A).mul_mem_right _ hπm) he4m he3 he4 (by simp [h6])
    simpa using pow_ne_zero 2 he3m

end FLT.Mazur
