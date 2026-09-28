/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Data.ENat.BigOperators
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic

/-!
# A discrete obstruction to polynomial values

For a finite family of conjugates, the sum and maximum of the valuations of
pairwise differences are independent of the chosen conjugate. The value of
the product of distances to this family cannot be one step below the sum of
these two invariants. This gives the discrete part of Fontaine's perturbed
polynomial argument without introducing ramification functions.
-/

public section

namespace AddValuation

variable {R : Type*} [Ring R] {Γ : Type*} [LinearOrderedAddCommMonoidWithTop Γ]

/-- The distance from a point to another root is computed from a nearest root. -/
theorem subEqMinOfNearest (v : AddValuation R Γ) (x a b : R)
    (hnear : v (x - b) ≤ v (x - a)) :
    v (x - b) = min (v (x - a)) (v (a - b)) := by
  have heq : x - a + (a - b) = x - b := sub_add_sub_cancel _ _ _
  rcases lt_trichotomy (v (x - a)) (v (a - b)) with h | h | h
  · rw [← heq, v.map_add_eq_of_lt_left h, min_eq_left h.le]
  · apply le_antisymm
    · simpa only [← h, min_self] using hnear
    · simpa only [heq] using v.map_add (x - a) (a - b)
  · rw [← heq, v.map_add_eq_of_lt_right h, min_eq_right h.le]

end AddValuation

namespace Finset

/-- A truncated distance sum omits the integer one step below its final break. -/
theorem sumMinNeSumAddMaxSubOne {ι : Type*}
    (s : Finset ι) (k : ι → ℕ) (c t : ℕ)
    (hbound : ∀ i ∈ s, k i ≤ c) (hmax : ∃ i ∈ s, k i = c) (hc : 0 < c) :
    t + ∑ i ∈ s, min t (k i) ≠ (∑ i ∈ s, k i) + c - 1 := by
  by_cases ht : c ≤ t
  · have hs : ∑ i ∈ s, min t (k i) = ∑ i ∈ s, k i := by
      apply sum_congr rfl
      intro i hi
      exact min_eq_right ((hbound i hi).trans ht)
    rw [hs]
    omega
  · obtain ⟨j, hj, hkj⟩ := hmax
    have hs : (∑ i ∈ s, min t (k i)) < ∑ i ∈ s, k i := by
      apply sum_lt_sum
      · intro i _
        exact min_le_right _ _
      · exact ⟨j, hj, by rw [hkj, min_eq_left (by omega)]; omega⟩
    omega

end Finset

namespace AddValuation

variable {R : Type*} [CommRing R]

/-- An additive valuation takes a finite product to the sum of its values. -/
theorem mapProdNatTop (v : AddValuation R ℕ∞) {ι : Type*}
    (s : Finset ι) (f : ι → R) : v (∏ i ∈ s, f i) = ∑ i ∈ s, v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

open scoped Classical in
/-- The product of distances to a family with constant pairwise valuation
sum and maximum cannot have valuation one step below their sum. -/
theorem prodSubNeCritical (v : AddValuation R ℕ∞) {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : ι → R) (k : ι → ι → ℕ) (d c : ℕ)
    (hdiff : ∀ i j, j ≠ i → v (a i - a j) = k i j)
    (hsum : ∀ i, ∑ j ∈ Finset.univ.erase i, k i j = d)
    (hbound : ∀ i j, j ≠ i → k i j ≤ c)
    (hmax : ∀ i, ∃ j, j ≠ i ∧ k i j = c) (hc : 0 < c) (x : R) :
    v (∏ i, (x - a i)) ≠ ((d + c - 1 : ℕ) : ℕ∞) := by
  classical
  intro h
  rw [v.mapProdNatTop] at h
  have hfinite : ∀ i, v (x - a i) ≠ ⊤ := by
    have hf : (∑ i, v (x - a i)) ≠ ⊤ := by rw [h]; exact ENat.natCast_ne_top _
    exact fun i ↦ ENat.sum_ne_top.mp hf i (Finset.mem_univ _)
  choose t ht using fun i ↦ ENat.ne_top_iff_exists.mp (hfinite i)
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ t Finset.univ_nonempty
  have hnear : ∀ j, v (x - a j) ≤ v (x - a i) := by
    intro j
    rw [← ht j, ← ht i, Nat.cast_le]
    exact hi j (Finset.mem_univ _)
  have hmin : ∀ j ∈ Finset.univ.erase i, t j = min (t i) (k i j) := by
    intro j hj
    have hv := v.subEqMinOfNearest x (a i) (a j) (hnear j)
    rw [← ht j, ← ht i, hdiff i j (Finset.mem_erase.mp hj).1] at hv
    by_cases hle : t i ≤ k i j
    · rw [min_eq_left hle]
      rw [min_eq_left (Nat.cast_le.mpr hle)] at hv
      exact ENat.natCast_inj.mp hv
    · have hle' : k i j ≤ t i := by omega
      rw [min_eq_right hle']
      rw [min_eq_right (Nat.cast_le.mpr hle')] at hv
      exact ENat.natCast_inj.mp hv
  have htSum : ∑ j, t j = d + c - 1 := by
    apply ENat.natCast_inj.mp
    simpa only [Nat.cast_sum, ht] using h
  have heq : t i + ∑ j ∈ Finset.univ.erase i, min (t i) (k i j) = d + c - 1 := by
    rw [← Finset.sum_congr rfl hmin]
    rw [Finset.add_sum_erase _ _ (Finset.mem_univ _)]
    exact htSum
  apply Finset.sumMinNeSumAddMaxSubOne (Finset.univ.erase i) (k i) c (t i)
    (fun j hj ↦ hbound i j (Finset.mem_erase.mp hj).1) ?_ hc
  · simpa only [hsum i] using heq
  · obtain ⟨j, hji, hj⟩ := hmax i
    exact ⟨j, Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩, hj⟩

end AddValuation

namespace AddValuation

variable {R G : Type*} [CommRing R] [Group G] [Fintype G] [MulSemiringAction G R]

open scoped Classical in
/-- For an orbit under valuation-preserving automorphisms, one row of
pairwise distances determines the forbidden product valuation. -/
theorem orbitProdSubNeCritical (v : AddValuation R ℕ∞)
    (hv : ∀ (g : G) (z : R), v (g • z) = v z)
    (a : R) (k : G → ℕ) (d c : ℕ)
    (hk : ∀ g, g ≠ 1 → v (a - g • a) = k g)
    (hsum : ∑ g ∈ Finset.univ.erase 1, k g = d)
    (hbound : ∀ g, g ≠ 1 → k g ≤ c)
    (hmax : ∃ g, g ≠ 1 ∧ k g = c) (hc : 0 < c) (x : R) :
    v (∏ g : G, (x - g • a)) ≠ ((d + c - 1 : ℕ) : ℕ∞) := by
  classical
  apply v.prodSubNeCritical (fun g : G ↦ g • a) (fun i j ↦ k (i⁻¹ * j)) d c
  · intro i j hji
    rw [← hv i⁻¹ (i • a - j • a)]
    simpa only [smul_sub, smul_smul, inv_mul_cancel, one_smul] using
      hk (i⁻¹ * j) (by intro h; apply hji; simpa using congrArg (fun z ↦ i * z) h)
  · intro i
    rw [← hsum]
    apply Finset.sum_equiv (Equiv.mulLeft i⁻¹)
    · intro j
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      change j ≠ i ↔ i⁻¹ * j ≠ 1
      constructor
      · intro hji h
        apply hji
        simpa using congrArg (fun z ↦ i * z) h
      · rintro h rfl
        exact h (inv_mul_cancel _)
    · intro j _
      rfl
  · intro i j hji
    exact hbound _ (by intro h; apply hji; simpa using congrArg (fun z ↦ i * z) h)
  · intro i
    obtain ⟨g, hg, hkg⟩ := hmax
    refine ⟨i * g, ?_, ?_⟩
    · simpa using hg
    · simpa only [inv_mul_cancel_left] using hkg
  · exact hc

end AddValuation
