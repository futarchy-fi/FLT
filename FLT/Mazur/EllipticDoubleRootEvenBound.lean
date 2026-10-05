/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticDoubleRootEvenComparison
public import FLT.Mazur.EllipticDoubleRootOddBound
public import FLT.Mazur.QuadraticComponentBound

/-!
# Termination at an even double-root stage

With a₆ zero, exact depth k+3 of a₄ makes the residual x-quadratic
separable. Its two possible labels inject the deep component classes into
two roots, giving the actual bound four after the simple class is included.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

/-- Exact depth of a₄ terminates any even double-root stage with bound four. -/
theorem normalizedDoubleRoot_even_components {K : Type*} [Field K]
    (A : ValuationSubring K) (W : WeierstrassCurve A) {π : A} (hπ : π ≠ 0)
    (hgen : maximalIdeal A = Ideal.span {π}) (e2 : A)
    (h1 : W.a₁ ∈ maximalIdeal A) (h2 : W.a₂ = π * e2) (h2m : e2 ∉ maximalIdeal A)
    (k : ℕ) (h3 : W.a₃ ∈ maximalIdeal A ^ (k + 3))
    (h4 : W.a₄ ∈ maximalIdeal A ^ (k + 3))
    (h4' : W.a₄ ∉ maximalIdeal A ^ (k + 4)) (h6 : W.a₆ = 0) :
    Finite (EllipticComponentQuotient A W) ∧ Nat.card (EllipticComponentQuotient A W) ≤ 4 := by
  classical
  obtain ⟨e1, he1⟩ := exists_node_coordinate_factor hgen 1 (by simpa using h1)
  obtain ⟨e3, he3⟩ := exists_node_coordinate_factor hgen (k + 3) h3
  obtain ⟨e4, he4⟩ := exists_node_coordinate_factor hgen (k + 3) h4
  have hπm : π ∈ maximalIdeal A := hgen ▸ Ideal.mem_span_singleton_self π
  have he4m : residue A e4 ≠ 0 := by
    intro hz
    apply h4'
    rw [he4, pow_succ]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hπm (k + 3)) ((residue_eq_zero_iff _).mp hz)
  have he2m : residue A e2 ≠ 0 := fun hz => h2m ((residue_eq_zero_iff _).mp hz)
  let S := DoubleRootSimpleClass A W π e2
  let D := {c : EllipticComponentQuotient A W // c ≠ 0 ∧ ¬ S c}
  have hex (c : D) : ∃ P, ∃ _v : DoubleRootEvenCoordinates A W π k P,
      ellipticComponentHom A W P = c.val := by
    obtain ⟨P, hP⟩ := ellipticComponentHom_surjective A W c.val
    have hPs : ¬ SmoothReduction A W P := fun hs =>
      c.property.1 (hP.symm.trans ((ellipticComponentHom_eq_zero A W P).mpr hs))
    rcases doubleRoot_simple_or_deep_coordinates A W hπ hgen e2 h1 h2 h2m k
        (Ideal.pow_le_pow_right (by omega) h3) h4 h6 P hPs with hs | hv
    · obtain ⟨v, hv⟩ := hs
      exact False.elim (c.property.2 ⟨P, v, hv, hP⟩)
    · obtain ⟨v⟩ := hv
      obtain ⟨w⟩ := v.exists_doubleRootEvenCoordinates hπ hgen h1
        (h2 ▸ (maximalIdeal A).mul_mem_right _ hπm) h3 h4 (by simp [h6])
      exact ⟨P, w, hP⟩
  choose P v hv using hex
  let f : D → ResidueField A := fun c => residue A (v c).x
  have hr (c : D) : residue A e2 * f c ^ 2 + residue A e4 * f c + 0 = 0 := by
    simpa only [map_zero] using doubleRoot_even_scaled_residue W hπ hπm k
      (v c).x (v c).y e2 e3 e4 0 h1 h2 he3 he4 (by simp [h6]) (v c).equation
  have hd (c : D) : 2 * residue A e2 * f c + residue A e4 ≠ 0 :=
    quadratic_root_simple_of_discr (hr c) (by simpa using pow_ne_zero 2 he4m)
  apply finite_card_le_four_of_simple_or_quadratic S
    (doubleRootSimpleClass_unique A W hπ hgen e2 h1 h2 h2m
      (Ideal.pow_le_pow_right (by omega) h3) (Ideal.pow_le_pow_right (by omega) h4) h6)
    (residue A e2) (residue A e4) 0 he2m f _ hr
  intro c d he
  apply Subtype.ext
  rw [← hv c, ← hv d]
  exact (v c).component_eq_of_same (v d) hπ hπm e1 e2 e3 e4
    (by simpa using he1) h2 he3 he4 (by simp [h6]) he (hd c)

end FLT.Mazur
