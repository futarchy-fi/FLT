/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticStarZeroCoordinates
public import FLT.Mazur.CubicComponentBound

/-!
# The normalized I₀* rational component bound

For the coefficient depths (1,1,2,2,3), a nonzero discriminant of the residual
cubic gives a finite actual component quotient, killed by two and of order
at most four. The cubic need not split over the residue field.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)

/-- The normalized I₀* coefficient and cubic discriminant tests bound the actual quotient. -/
theorem normalizedStarZero_components {π : A} (hπ : π ≠ 0)
    (hgen : maximalIdeal A = Ideal.span {π}) (e1 e2 e3 e4 e6 : A)
    (h1 : W.a₁ = π * e1) (h2 : W.a₂ = π * e2)
    (h3 : W.a₃ = π ^ 2 * e3) (h4 : W.a₄ = π ^ 2 * e4) (h6 : W.a₆ = π ^ 3 * e6)
    (hd : (Cubic.mk 1 (residue A e2) (residue A e4) (residue A e6)).discr ≠ 0) :
    Finite (EllipticComponentQuotient A W) ∧
      (∀ c : EllipticComponentQuotient A W, 2 • c = 0) ∧
      Nat.card (EllipticComponentQuotient A W) ≤ 4 := by
  classical
  let G := EllipticComponentQuotient A W
  have hπm : π ∈ maximalIdeal A := hgen ▸ Ideal.mem_span_singleton_self π
  have hm (a : A) : π * a ∈ maximalIdeal A := (maximalIdeal A).mul_mem_right _ hπm
  have h1m : W.a₁ ∈ maximalIdeal A := h1 ▸ hm e1
  have h2m : W.a₂ ∈ maximalIdeal A := h2 ▸ hm e2
  have h6m : W.a₆ ∈ maximalIdeal A := by
    rw [h6, pow_succ', mul_assoc]
    exact hm _
  have hex (c : {c : G // c ≠ 0}) :
      ∃ P, ∃ _v : StarZeroCoordinates A W π P, ellipticComponentHom A W P = c.val := by
    obtain ⟨P, hP⟩ := ellipticComponentHom_surjective A W c.val
    have hPs : ¬ SmoothReduction A W P := by
      intro hs
      exact c.property (hP.symm.trans ((ellipticComponentHom_eq_zero A W P).mpr hs))
    obtain ⟨v⟩ := exists_starZeroCoordinates A W hπ hgen e3 e4 e6 h1m h2m h3 h4 h6 P hPs
    exact ⟨P, v, hP⟩
  choose P v hv using hex
  let f : {c : G // c ≠ 0} → ResidueField A := fun c => residue A (v c).x
  have hr (c : {c : G // c ≠ 0}) :
      f c ^ 3 + residue A e2 * f c ^ 2 + residue A e4 * f c + residue A e6 = 0 :=
    starZero_scaled_residue W hπ hπm (v c).x (v c).y e2 e3 e4 e6 h1m h2 h3 h4 h6
      (v c).equation
  have hs (c : {c : G // c ≠ 0}) :
      3 * f c ^ 2 + 2 * residue A e2 * f c + residue A e4 ≠ 0 :=
    monicCubic_root_simple_of_discr_ne_zero (hr c) hd
  have hf : Function.Injective f := by
    intro c d he
    apply Subtype.ext
    rw [← hv c, ← hv d]
    exact (v c).component_eq_of_same (v d) hπ hπm e1 e2 e3 e4 h1 h2 h3 h4 h6m he (hs c)
  obtain ⟨hfinite, hcard⟩ := finite_card_le_four_of_cubic_labels
    (Cubic.mk 1 (residue A e2) (residue A e4) (residue A e6))
    (Cubic.ne_zero_of_a_ne_zero (by exact one_ne_zero)) f hf (fun c => by simpa using hr c)
  refine ⟨hfinite, fun c => ?_, hcard⟩
  by_cases hc : c = 0
  · simp [hc]
  · let d : {c : G // c ≠ 0} := ⟨c, hc⟩
    have he : ellipticComponentHom A W (P d) = c := hv d
    rw [← he, nsmul_ellipticComponentHom_eq_zero_iff, two_nsmul]
    exact (v d).smooth_add_of_same (v d) hπ hπm e1 e2 e3 e4 h1 h2 h3 h4 h6m rfl (hs d)

end FLT.Mazur
