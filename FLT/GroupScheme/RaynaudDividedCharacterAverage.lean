/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudDividedGroupGenerator

/-!
# Dividing the formal fundamental average by p

The group-generator calculation and the mixed-binomial cancellation give
an actual divided power. If the character reduces to an embedding, its
Frobenius additive evaluation is -1.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan.CharacterAverage

variable {R S F : Type*} [CommRing R] [CommRing S] [Algebra R S] [Field F]
  [Fintype Fˣ] [Invertible (Fintype.card Fˣ : R)]
  (p : ℕ) [Fact p.Prime] [CharP F p] [CharP S p]
  (χ : Fˣ →* Rˣ) (e : F →+* S)

/-- The formal p-th power has a divided power with Frobenius evaluation -1. -/
theorem formalAverage_dividedPower
    (he : ∀ u : Fˣ, algebraMap R S (χ u) = e u) :
    ∃ z : AddMonoidAlgebra R F, formalAverage χ ^ p = (p : R) • z ∧
      additiveEvaluation ((frobenius S p).comp e).toAddMonoidHom z = -1 := by
  let E := ((frobenius S p).comp e).toAddMonoidHom
  let w (u : Fˣ) : R := (↑(χ u)⁻¹ : R)
  let t (u : Fˣ) : AddMonoidAlgebra R F := AddMonoidAlgebra.single (u : F) 1 - 1
  choose z hz hez using fun u : Fˣ ↦
    dividedPower_single_sub_one (R := R) p (Fact.out : p.Prime) E (u : F)
  obtain ⟨q, hq, heq⟩ := dividedPower_sum p (Fact.out : p.Prime) E Finset.univ
    (fun u ↦ w u • t u) (fun u ↦ w u ^ p • z u)
    (by intro u hu; simp [t])
    (by intro u hu; exact dividedPower_smul p (w u) (t u) (z u) (hz u))
  refine ⟨⅟(Fintype.card Fˣ : R) ^ p • q, ?_, ?_⟩
  · exact dividedPower_smul p _ _ _ hq
  · rw [map_smul, heq]
    simp_rw [map_smul, hez]
    have hw (u : Fˣ) : (w u ^ p) • -E (u : F) = -(1 : S) := by
      rw [Algebra.smul_def]
      change algebraMap R S (w u ^ p) * -(e u ^ p) = -1
      rw [map_pow, mul_neg, ← mul_pow]
      have h : algebraMap R S (w u) * e u = 1 := by
        rw [← he, ← map_mul]
        simp [w]
      rw [h, one_pow]
    simp_rw [hw]
    rw [Algebra.smul_def]
    change algebraMap R S (⅟(Fintype.card Fˣ : R) ^ p) *
      (∑ _ : Fˣ, -(1 : S)) = -1
    have hc : (Fintype.card Fˣ : S) ^ p = (Fintype.card Fˣ : S) := by
      exact map_natCast (frobenius S p) (Fintype.card Fˣ)
    rw [Finset.sum_const, Finset.card_univ, smul_neg, nsmul_one,
      mul_neg, map_pow, ← hc, ← mul_pow]
    have hqinv : algebraMap R S ⅟(Fintype.card Fˣ : R) * (Fintype.card Fˣ : S) = 1 := by
      rw [← map_natCast (algebraMap R S), ← map_mul, invOf_mul_self, map_one]
    rw [hqinv, one_pow]

end ThreeAdicPlan.CharacterAverage
