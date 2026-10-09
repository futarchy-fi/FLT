/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXFlat
public import Mathlib.RingTheory.Ideal.Colon

/-!
# Saturation of the x-direction total-transform relations

The incidence equation and x² times the divided cubic have saturation exactly
the strict-transform ideal. The reverse inclusion needs only multiplication
by x²; the forward inclusion uses proved regularity of x in the actual chart.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace FLT.Mazur.WeierstrassSuccessiveX

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)

/-- The incidence relation together with the undivided cubic factor. -/
def totalRelations : Ideal (MvPolynomial (Fin 3) R) :=
  Ideal.span {X 0 * X 2 - C π, X 2 ^ 2 * equationPolynomial W s b3 b4 b6}

/-- The total-transform relations vanish in the strict presentation. -/
theorem totalRelations_le_relations :
    totalRelations W s π b3 b4 b6 ≤ relations W s π b3 b4 b6 := by
  apply Ideal.span_le.mpr
  intro p hp
  rcases Set.mem_insert_iff.mp hp with rfl | hp
  · exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  · have hp' := Set.mem_singleton_iff.mp hp
    subst p
    exact Ideal.mul_mem_left _ _
      (Ideal.subset_span (Set.mem_insert _ _))

/-- Multiplying any strict relation by x² gives an actual total-transform relation. -/
theorem horizontal_sq_mul_mem_total {p : MvPolynomial (Fin 3) R}
    (hp : p ∈ relations W s π b3 b4 b6) :
    X 2 ^ 2 * p ∈ totalRelations W s π b3 b4 b6 := by
  have h : relations W s π b3 b4 b6 ≤ (totalRelations W s π b3 b4 b6).colon {X 2 ^ 2} := by
    apply Ideal.span_le.mpr
    intro q hq
    apply Submodule.mem_colon_singleton.mpr
    change q * X 2 ^ 2 ∈ totalRelations W s π b3 b4 b6
    rcases Set.mem_insert_iff.mp hq with rfl | hq
    · rw [mul_comm]
      exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    · have hq' := Set.mem_singleton_iff.mp hq
      subst q
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))
  simpa only [smul_eq_mul, mul_comm] using Submodule.mem_colon_singleton.mp (h hp)

variable [IsDomain R]

/-- Horizontal powers cannot move a nonrelation into the strict-transform ideal. -/
theorem horizontal_pow_mul_mem_strict_iff (hπ : π ≠ 0) (n : ℕ)
    (p : MvPolynomial (Fin 3) R) :
    X 2 ^ n * p ∈ relations W s π b3 b4 b6 ↔ p ∈ relations W s π b3 b4 b6 := by
  constructor
  · intro h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hz := Ideal.Quotient.eq_zero_iff_mem.mpr h
    rw [map_mul, map_pow] at hz
    change coord W s π b3 b4 b6 2 ^ n * Ideal.Quotient.mk _ p = 0 at hz
    exact ((u_regular W s π b3 b4 b6 hπ).pow n).left
      (hz.trans (mul_zero _).symm)
  · exact fun h => Ideal.mul_mem_left _ _ h

/-- Saturating the total transform by the original horizontal variable gives precisely
 the actual strict equation chart. -/
theorem totalRelations_saturation (hπ : π ≠ 0) (p : MvPolynomial (Fin 3) R) :
    (∃ n : ℕ, X 2 ^ n * p ∈ totalRelations W s π b3 b4 b6) ↔
      p ∈ relations W s π b3 b4 b6 := by
  constructor
  · rintro ⟨n, hn⟩
    exact (horizontal_pow_mul_mem_strict_iff W s π b3 b4 b6 hπ n p).mp
      (totalRelations_le_relations W s π b3 b4 b6 hn)
  · exact fun hp => ⟨2, horizontal_sq_mul_mem_total W s π b3 b4 b6 hp⟩

end FLT.Mazur.WeierstrassSuccessiveX
