/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.Algebra.Polynomial.Taylor

/-! # Ultrametric coefficient estimates without a combinatorial loss -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
open Polynomial
variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- A multiset sum has the same bound as its summands, including repetitions. -/
theorem ultrametric_multiset_sum_le (s : Multiset K) {r : ℝ} (hr : 0 ≤ r)
    (hs : ∀ x ∈ s, ‖x‖ ≤ r) : ‖s.sum‖ ≤ r := by
  induction s using Multiset.induction_on with
  | empty => simpa using hr
  | @cons a s ih =>
    rw [Multiset.sum_cons]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (hs a (by simp)) (ih (fun x hx ↦ hs x (by simp [hx]))))

omit [IsUltrametricDist K] in
/-- A product of bounded factors has the corresponding power bound. -/
theorem norm_multiset_prod_le_pow (s : Multiset K) {r : ℝ} (hr : 0 ≤ r)
    (hs : ∀ x ∈ s, ‖x‖ ≤ r) : ‖s.prod‖ ≤ r ^ s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    rw [Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ']
    exact mul_le_mul (hs a (by simp)) (ih (fun x hx ↦ hs x (by simp [hx])))
      (norm_nonneg _) hr

/-- Elementary symmetric functions have no binomial loss in an ultrametric field. -/
theorem norm_multiset_esymm_le (s : Multiset K) {r : ℝ} (hr : 0 ≤ r)
    (hs : ∀ x ∈ s, ‖x‖ ≤ r) (k : ℕ) : ‖s.esymm k‖ ≤ r ^ k := by
  unfold Multiset.esymm
  apply ultrametric_multiset_sum_le _ (pow_nonneg hr _)
  intro x hx
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hx
  obtain ⟨hts, htk⟩ := Multiset.mem_powersetCard.mp ht
  rw [← htk]
  exact norm_multiset_prod_le_pow t hr (fun x hx ↦ hs x (Multiset.mem_of_le hts hx))

/-- Coefficients of a product of linear factors are bounded by powers of the root bound. -/
theorem norm_coeff_prod_X_add_C_le (s : Multiset K) {r : ℝ} (hr : 0 ≤ r)
    (hs : ∀ x ∈ s, ‖x‖ ≤ r) {k : ℕ} (hk : k ≤ s.card) :
    ‖((s.map fun x ↦ X + C x).prod).coeff k‖ ≤ r ^ (s.card - k) := by
  rw [Multiset.prod_X_add_C_coeff s hk]
  exact norm_multiset_esymm_le s hr hs _

/-- Hasse evaluation is bounded by root displacements, with no degree-dependent factor. -/
theorem norm_hasseDeriv_eval_le (f : K[X]) (hf : f.Monic) (hsplit : f.Splits)
    (a : K) {r : ℝ} (hr : 0 ≤ r) (hroots : ∀ b ∈ f.roots, ‖a - b‖ ≤ r)
    {j : ℕ} (hj : j ≤ f.natDegree) :
    ‖(hasseDeriv j f).eval a‖ ≤ r ^ (f.natDegree - j) := by
  have ht : taylor a f = ((f.roots.map (fun b ↦ a - b)).map fun x ↦ X + C x).prod := by
    conv_lhs => rw [hsplit.eq_prod_roots_of_monic hf]
    rw [taylor_apply]
    simp only [multiset_prod_comp, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro b _
    simp [sub_eq_add_neg, add_assoc]
  rw [← taylor_coeff, ht]
  have hc := hsplit.natDegree_eq_card_roots
  simpa only [Multiset.card_map, ← hc] using
    norm_coeff_prod_X_add_C_le (f.roots.map (fun b ↦ a - b)) hr
      (by
        intro x hx
        obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.mp hx
        exact hroots b hb)
      (by simpa only [Multiset.card_map, ← hc] using hj)

end PadicHodgeTheory
