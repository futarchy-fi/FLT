/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Complex conjugation on the rational algebraic closure

Restrict complex conjugation along an embedding of the rational algebraic closure.
Its cyclotomic character is minus one.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

/-- A fixed complex embedding of the rational algebraic closure. -/
def rationalClosureEmbedding : AlgebraicClosure ℚ →ₐ[ℚ] ℂ := IsAlgClosed.lift

/-- The complex numbers as an algebra over the chosen rational algebraic closure. -/
local instance complexClosureAlgebra : Algebra (AlgebraicClosure ℚ) ℂ :=
  rationalClosureEmbedding.toRingHom.toAlgebra

/-- The complex embedding respects the rational scalar tower. -/
local instance complexClosureScalarTower : IsScalarTower ℚ (AlgebraicClosure ℚ) ℂ :=
  IsScalarTower.of_algebraMap_eq' rationalClosureEmbedding.comp_algebraMap.symm

/-- Complex conjugation restricted to the rational algebraic closure. -/
def rationalComplexConjugation : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ :=
  (Complex.conjAe.restrictScalars ℚ).restrictNormal (AlgebraicClosure ℚ)

/-- Complex conjugation sends every root of unity to its inverse. -/
theorem rationalComplexConjugation_root {n : ℕ} [NeZero n]
    (t : (AlgebraicClosure ℚ)ˣ) (ht : t ∈ rootsOfUnity n (AlgebraicClosure ℚ)) :
    rationalComplexConjugation t = (t : AlgebraicClosure ℚ)⁻¹ := by
  apply (algebraMap (AlgebraicClosure ℚ) ℂ).injective
  rw [show algebraMap (AlgebraicClosure ℚ) ℂ (rationalComplexConjugation t) =
      starRingEnd ℂ (algebraMap (AlgebraicClosure ℚ) ℂ t) from
    AlgEquiv.restrictNormal_commutes _ _ _, map_inv₀]
  let u := Units.map (algebraMap (AlgebraicClosure ℚ) ℂ).toMonoidHom t
  have hu : u ∈ rootsOfUnity n ℂ := by
    rw [mem_rootsOfUnity] at ht ⊢
    change (Units.map (algebraMap (AlgebraicClosure ℚ) ℂ).toMonoidHom t) ^ n = 1
    rw [← map_pow, ht, map_one]
  simpa [u] using Complex.conj_rootsOfUnity hu

/-- The cyclotomic value of rational complex conjugation is minus one. -/
theorem rationalComplexConjugation_cyclotomic (p : ℕ) [Fact p.Prime] :
    (cyclotomicCharacter (AlgebraicClosure ℚ) p
      rationalComplexConjugation.toRingEquiv).val = -1 := by
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  rw [map_neg, map_one, cyclotomicCharacter.toZModPow]
  symm
  apply modularCyclotomicCharacter.unique
  intro t ht
  rw [show rationalComplexConjugation.toRingEquiv t = (t : AlgebraicClosure ℚ)⁻¹ from
    rationalComplexConjugation_root t ht]
  have hp : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos _
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  rw [hm, ZMod.val_neg_one]
  apply (mul_left_cancel₀ (Units.ne_zero t))
  rw [mul_inv_cancel₀ (Units.ne_zero t), ← pow_succ']
  rw [mem_rootsOfUnity] at ht
  simpa only [hm, Units.val_pow_eq_pow_val, Units.val_one] using
    (congrArg Units.val ht).symm

end ThreeAdicPlan
