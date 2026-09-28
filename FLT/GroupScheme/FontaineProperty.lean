/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.LocalPointField
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Fontaine's embedding property over the three-adic integers

The ideal `threeAdicValuationIdeal E m` consists of integral elements of
normalized valuation at least `m`, expressed as the spectral-norm inequality
`|x| ≤ 3 ^ (-m)`. Thus zero belongs to every such ideal.

`FontaineProperty A m` says that an algebra map from `A` into any finite
extension's integers modulo this ideal implies the existence of an algebra
map into those integers. It does not require the new map to reduce to the
given map. Exact lifting is a stronger assertion and is not Fontaine's
embedding property. No different bound is asserted in this file.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable (E : Type*) [Field E] [Algebra ℚ_[3] E] [Algebra ℤ_[3] E]
  [IsScalarTower ℤ_[3] ℚ_[3] E] [FiniteDimensional ℚ_[3] E]

/-- Integral elements whose valuation, normalized by `v(3) = 1`, is at least `m`. -/
def threeAdicValuationIdeal (m : ℚ) : Ideal (ThreeAdicIntegers E) where
  carrier := {x | spectralNorm ℚ_[3] E (x : E) ≤ (3 : ℝ) ^ (-(m : ℝ))}
  zero_mem' := by simp [spectralNorm_zero, Real.rpow_nonneg]
  add_mem' hx hy := (isNonarchimedean_spectralNorm _ _).trans (max_le hx hy)
  smul_mem' a b hb := by
    change spectralNorm ℚ_[3] E ((a : E) * (b : E)) ≤ _
    apply (spectralNorm_mul (Algebra.IsAlgebraic.isAlgebraic (R := ℚ_[3]) (a : E))
      (Algebra.IsAlgebraic.isAlgebraic (R := ℚ_[3]) (b : E))).trans
    exact (mul_le_mul_of_nonneg_right
      ((isIntegral_iff_spectralNorm_le_one E (a : E)).mp a.property)
      (spectralNorm_nonneg _)).trans (by simpa using hb)

/-- Membership is the closed spectral-norm cutoff, including the boundary. -/
@[simp] theorem mem_threeAdicValuationIdeal (m : ℚ) (x : ThreeAdicIntegers E) :
    x ∈ threeAdicValuationIdeal E m ↔
      spectralNorm ℚ_[3] E (x : E) ≤ (3 : ℝ) ^ (-(m : ℝ)) := Iff.rfl

/-- Increasing the valuation cutoff decreases the ideal. -/
theorem threeAdicValuationIdeal_antitone : Antitone (threeAdicValuationIdeal E) := by
  intro m n h x hx
  exact hx.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num)
    (neg_le_neg (Rat.cast_le.mpr h)))

/-- The cutoff uses the normalization `v(3^k) = k`. -/
theorem three_pow_mem_threeAdicValuationIdeal (k : ℕ) (m : ℚ) :
    (3 : ThreeAdicIntegers E) ^ k ∈ threeAdicValuationIdeal E m ↔ m ≤ k := by
  rw [mem_threeAdicValuationIdeal]
  change spectralNorm ℚ_[3] E ((3 : E) ^ k) ≤ _ ↔ _
  have h := spectralNorm_extends (K := ℚ_[3]) (L := E) ((3 : ℚ_[3]) ^ k)
  simp only [map_pow, map_ofNat] at h
  rw [h]
  have hp := Padic.norm_p_pow (p := 3) k
  norm_num only [Nat.cast_ofNat] at hp
  rw [hp, ← Real.rpow_intCast]
  simp only [Int.cast_neg, Int.cast_natCast]
  rw [Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 3), neg_le_neg_iff]
  exact_mod_cast (Iff.rfl : m ≤ k ↔ m ≤ k)

/-- At cutoff zero every integral element belongs to the ideal. -/
@[simp] theorem threeAdicValuationIdeal_zero : threeAdicValuationIdeal E 0 = ⊤ := by
  apply top_unique
  intro x _
  simpa using (isIntegral_iff_spectralNorm_le_one E (x : E)).mp x.property

/-- For a positive cutoff, the valuation ideal is proper. -/
theorem threeAdicValuationIdeal_ne_top {m : ℚ} (hm : 0 < m) :
    threeAdicValuationIdeal E m ≠ ⊤ := by
  rw [Ideal.ne_top_iff_one]
  change ¬ spectralNorm ℚ_[3] E 1 ≤ (3 : ℝ) ^ (-(m : ℝ))
  rw [spectralNorm_one, not_le]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by exact_mod_cast neg_neg_of_pos hm)

variable (A : Type) [CommRing A] [Algebra ℤ_[3] A]

/-- Fontaine's `P_m`: an approximate integral point over a finite extension
implies an integral point over the same extension, without prescribing its reduction. -/
def FontaineProperty (m : ℚ) : Prop :=
  ∀ (E : Type) [Field E] [Algebra ℚ_[3] E] [Algebra ℤ_[3] E]
    [IsScalarTower ℤ_[3] ℚ_[3] E] [FiniteDimensional ℚ_[3] E],
    Nonempty (A →ₐ[ℤ_[3]] ThreeAdicIntegers E ⧸ threeAdicValuationIdeal E m) →
      Nonempty (A →ₐ[ℤ_[3]] ThreeAdicIntegers E)

/-- The embedding property persists when the precision increases. -/
theorem FontaineProperty.mono {m n : ℚ} (h : FontaineProperty A m) (hmn : m ≤ n) :
    FontaineProperty A n := by
  intro E _ _ _ _ _ ⟨f⟩
  exact h E ⟨(Ideal.Quotient.factorₐ ℤ_[3]
    (threeAdicValuationIdeal_antitone E hmn)).comp f⟩

/-- The base ring has the embedding property at every precision. -/
theorem fontaineProperty_base (m : ℚ) : FontaineProperty ℤ_[3] m := by
  intro E _ _ _ _ _ _
  exact ⟨Algebra.ofId ℤ_[3] (ThreeAdicIntegers E)⟩

/-- Isomorphic integral algebras have the same embedding property. -/
theorem fontaineProperty_iff_of_algEquiv {B : Type} [CommRing B] [Algebra ℤ_[3] B]
    (e : A ≃ₐ[ℤ_[3]] B) (m : ℚ) : FontaineProperty A m ↔ FontaineProperty B m := by
  constructor
  · intro h E _ _ _ _ _ ⟨f⟩
    obtain ⟨g⟩ := h E ⟨f.comp e.toAlgHom⟩
    exact ⟨g.comp e.symm.toAlgHom⟩
  · intro h E _ _ _ _ _ ⟨f⟩
    obtain ⟨g⟩ := h E ⟨f.comp e.symm.toAlgHom⟩
    exact ⟨g.comp e.toAlgHom⟩

end ThreeAdicPlan
