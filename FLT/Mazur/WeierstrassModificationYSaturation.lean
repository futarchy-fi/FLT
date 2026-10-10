/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationYRegular
public import Mathlib.RingTheory.Ideal.Colon

/-!
# Saturation of the y-direction total transform

Multiplying the divided cubic by the square of the retained vertical variable
recovers the total relation. Its saturation is the actual chart ideal, because
the original vertical coordinate is regular in the proved flat algebra.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace FLT.Mazur.WeierstrassModificationY

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)

/-- The incidence relation together with the undivided cubic factor. -/
def totalRelations : Ideal (MvPolynomial (Fin 3) R) :=
  Ideal.span {X 2 ^ 2 * equationPolynomial W b3 b4 b6, X 0 * X 2 - C s}

/-- The total-transform relations vanish in the strict presentation. -/
theorem totalRelations_le_relations :
    totalRelations W s b3 b4 b6 ≤ relations W s b3 b4 b6 := by
  apply Ideal.span_le.mpr
  intro p hp
  rcases Set.mem_insert_iff.mp hp with rfl | hp
  · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _))
  · have hp' := Set.mem_singleton_iff.mp hp
    subst p
    exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))

/-- Multiplying any strict relation by z² gives a total-transform relation. -/
theorem vertical_sq_mul_mem_total {p : MvPolynomial (Fin 3) R}
    (hp : p ∈ relations W s b3 b4 b6) :
    X 2 ^ 2 * p ∈ totalRelations W s b3 b4 b6 := by
  have h : relations W s b3 b4 b6 ≤ (totalRelations W s b3 b4 b6).colon {X 2 ^ 2} := by
    apply Ideal.span_le.mpr
    intro q hq
    apply Submodule.mem_colon_singleton.mpr
    change q * X 2 ^ 2 ∈ totalRelations W s b3 b4 b6
    rcases Set.mem_insert_iff.mp hq with rfl | hq
    · rw [mul_comm]
      exact Ideal.subset_span (Set.mem_insert _ _)
    · have hq' := Set.mem_singleton_iff.mp hq
      subst q
      exact Ideal.mul_mem_right _ _
        (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  simpa only [smul_eq_mul, mul_comm] using Submodule.mem_colon_singleton.mp (h hp)

variable [IsDomain R] [IsBezout R]
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

include h3 h4 h6

/-- Vertical powers cannot move a nonrelation into the strict-transform ideal. -/
theorem vertical_pow_mul_mem_strict_iff (hs : s ≠ 0) (n : ℕ)
    (p : MvPolynomial (Fin 3) R) :
    X 2 ^ n * p ∈ relations W s b3 b4 b6 ↔ p ∈ relations W s b3 b4 b6 := by
  constructor
  · intro h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hz := Ideal.Quotient.eq_zero_iff_mem.mpr h
    rw [map_mul, map_pow] at hz
    change coord W s b3 b4 b6 2 ^ n * Ideal.Quotient.mk _ p = 0 at hz
    exact ((vertical_regular W s b3 b4 b6 h3 h4 h6 hs).pow n).left
      (hz.trans (mul_zero _).symm)
  · exact fun h => Ideal.mul_mem_left _ _ h

/-- Saturating the total transform by the original vertical variable gives precisely
 the actual strict equation chart. -/
theorem totalRelations_saturation (hs : s ≠ 0) (p : MvPolynomial (Fin 3) R) :
    (∃ n : ℕ, X 2 ^ n * p ∈ totalRelations W s b3 b4 b6) ↔
      p ∈ relations W s b3 b4 b6 := by
  constructor
  · rintro ⟨n, hn⟩
    exact (vertical_pow_mul_mem_strict_iff W s b3 b4 b6 h3 h4 h6 hs n p).mp
      (totalRelations_le_relations W s b3 b4 b6 hn)
  · exact fun hp => ⟨2, vertical_sq_mul_mem_total W s b3 b4 b6 hp⟩

end FLT.Mazur.WeierstrassModificationY
