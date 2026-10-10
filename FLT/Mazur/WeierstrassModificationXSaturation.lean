/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXPresentation
public import Mathlib.RingTheory.Ideal.Colon

/-!
# Saturation of the x-direction total-transform relations

The incidence equation and x² times the divided cubic have saturation exactly
the strict-transform ideal. The reverse inclusion needs only multiplication
by x²; the forward inclusion uses proved regularity of x in the actual chart.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace FLT.Mazur.WeierstrassModificationX

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)

/-- The incidence relation together with the undivided cubic factor. -/
def totalRelations : Ideal (MvPolynomial (Fin 3) R) :=
  Ideal.span {incidencePolynomial s, X 2 ^ 2 * strictPolynomial W b3 b4 b6}

/-- The total-transform relations vanish in the strict presentation. -/
theorem totalRelations_le_strictRelations :
    totalRelations W s b3 b4 b6 ≤ strictRelations W s b3 b4 b6 := by
  apply Ideal.span_le.mpr
  intro p hp
  rcases Set.mem_insert_iff.mp hp with rfl | hp
  · exact Ideal.subset_span (Set.mem_insert _ _)
  · have hp' := Set.mem_singleton_iff.mp hp
    subst p
    exact Ideal.mul_mem_left _ _
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

/-- Multiplying any strict relation by x² gives an actual total-transform relation. -/
theorem horizontal_sq_mul_mem_total {p : MvPolynomial (Fin 3) R}
    (hp : p ∈ strictRelations W s b3 b4 b6) :
    X 2 ^ 2 * p ∈ totalRelations W s b3 b4 b6 := by
  have h : strictRelations W s b3 b4 b6 ≤ (totalRelations W s b3 b4 b6).colon {X 2 ^ 2} := by
    apply Ideal.span_le.mpr
    intro q hq
    apply Submodule.mem_colon_singleton.mpr
    change q * X 2 ^ 2 ∈ totalRelations W s b3 b4 b6
    rcases Set.mem_insert_iff.mp hq with rfl | hq
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))
    · have hq' := Set.mem_singleton_iff.mp hq
      subst q
      rw [mul_comm]
      exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  simpa only [smul_eq_mul, mul_comm] using Submodule.mem_colon_singleton.mp (h hp)

variable [IsDomain R]

/-- The retained original horizontal variable is regular in the strict presentation. -/
theorem strictCoord_horizontal_regular (hs : s ≠ 0) :
    IsRegular (strictCoord W s b3 b4 b6 2) := by
  let e := strictCoordinateEquiv W s b3 b4 b6
  have he : e (strictCoord W s b3 b4 b6 2) = x W s b3 b4 b6 :=
    fromStrictCoordinate_coord W s b3 b4 b6 2
  have hr := x_regular W s b3 b4 b6 hs
  refine ⟨?_, ?_⟩
  · intro a b h
    apply e.injective
    apply hr.left
    simpa only [map_mul, he] using congrArg e h
  · intro a b h
    apply e.injective
    apply hr.right
    simpa only [map_mul, he] using congrArg e h

/-- Horizontal powers cannot move a nonrelation into the strict-transform ideal. -/
theorem horizontal_pow_mul_mem_strict_iff (hs : s ≠ 0) (n : ℕ)
    (p : MvPolynomial (Fin 3) R) :
    X 2 ^ n * p ∈ strictRelations W s b3 b4 b6 ↔ p ∈ strictRelations W s b3 b4 b6 := by
  constructor
  · intro h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hz := Ideal.Quotient.eq_zero_iff_mem.mpr h
    rw [map_mul, map_pow] at hz
    change strictCoord W s b3 b4 b6 2 ^ n * Ideal.Quotient.mk _ p = 0 at hz
    exact ((strictCoord_horizontal_regular W s b3 b4 b6 hs).pow n).left
      (hz.trans (mul_zero _).symm)
  · exact fun h => Ideal.mul_mem_left _ _ h

/-- Saturating the total transform by the original horizontal variable gives precisely
 the actual strict equation chart. -/
theorem totalRelations_saturation (hs : s ≠ 0) (p : MvPolynomial (Fin 3) R) :
    (∃ n : ℕ, X 2 ^ n * p ∈ totalRelations W s b3 b4 b6) ↔
      p ∈ strictRelations W s b3 b4 b6 := by
  constructor
  · rintro ⟨n, hn⟩
    exact (horizontal_pow_mul_mem_strict_iff W s b3 b4 b6 hs n p).mp
      (totalRelations_le_strictRelations W s b3 b4 b6 hn)
  · exact fun hp => ⟨2, horizontal_sq_mul_mem_total W s b3 b4 b6 hp⟩

end FLT.Mazur.WeierstrassModificationX
