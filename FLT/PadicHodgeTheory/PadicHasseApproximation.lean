/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexGaloisAction
public import FLT.PadicHodgeTheory.PolynomialNearbyRoot
public import FLT.PadicHodgeTheory.UltrametricPolynomialCoefficients

/-! # Actual lower-degree approximants from Hasse derivatives -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
open Polynomial
variable (p : ℕ) [Fact p.Prime]

omit p [Fact p.Prime] in
/-- The Hasse derivative of a monic polynomial has its actual binomial leading coefficient. -/
theorem monic_hasseDeriv_leadingCoeff {K : Type*} [Field K] [CharZero K]
    (f : K[X]) (hf : f.Monic) {k : ℕ} (hk : k ≤ f.natDegree) :
    (hasseDeriv (f.natDegree - k) f).leadingCoeff = (f.natDegree.choose k : K) := by
  rw [leadingCoeff, natDegree_hasseDeriv, Nat.sub_sub_self hk, hasseDeriv_coeff,
    Nat.add_sub_of_le hk, hf.coeff_natDegree, mul_one, Nat.choose_symm hk]

/-- Hasse derivatives produce smaller-degree points, with the exact binomial loss exposed. -/
theorem padicHasse_exists_approximation (a : PadicAlgCl p) {r : ℝ} (hr : 0 ≤ r)
    (ha : ∀ σ : PadicGalois p, ‖σ a - a‖ ≤ r) {k : ℕ} (hk : 0 < k)
    (hkn : k ≤ (minpoly ℚ_[p] a).natDegree) :
    ∃ b : PadicAlgCl p, (minpoly ℚ_[p] b).natDegree ≤ k ∧
      ‖a - b‖ ^ k ≤ r ^ k / ‖((minpoly ℚ_[p] a).natDegree.choose k : ℚ_[p])‖ := by
  let f := minpoly ℚ_[p] a
  let q := hasseDeriv (f.natDegree - k) f
  let ι := algebraMap ℚ_[p] (PadicAlgCl p)
  have hf : f.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral a)
  have hqdeg : q.natDegree = k := by
    change (hasseDeriv (f.natDegree - k) f).natDegree = k
    rw [natDegree_hasseDeriv, Nat.sub_sub_self hkn]
  have hqmdeg : (q.map ι).natDegree = k := by rw [natDegree_map, hqdeg]
  obtain ⟨b, hb, hnear⟩ := polynomial_exists_nearby_root (q.map ι)
    (IsAlgClosed.splits _) (by omega) a
  have hq : q ≠ 0 := ne_zero_of_natDegree_gt (hqdeg ▸ hk)
  have hbroot : aeval b q = 0 := by
    simpa only [ι, IsRoot.def, eval_map_algebraMap] using
      (mem_roots (map_ne_zero hq)).mp hb
  have hbdeg : (minpoly ℚ_[p] b).natDegree ≤ k := by
    rw [← hqdeg]
    exact natDegree_le_natDegree (minpoly.degree_le_of_ne_zero ℚ_[p] b hq hbroot)
  have heval : ‖(q.map ι).eval a‖ ≤ r ^ k := by
    change ‖((hasseDeriv (f.natDegree - k) f).map ι).eval a‖ ≤ r ^ k
    rw [← hasseDeriv_map]
    have hbound := norm_hasseDeriv_eval_le (f.map ι) (hf.map ι)
      (IsAlgClosed.splits _) a hr (fun b hb ↦ ?_) (j := f.natDegree - k)
      (by rw [natDegree_map]; omega)
    · simpa only [natDegree_map,
        show f.natDegree - (f.natDegree - k) = k from Nat.sub_sub_self hkn] using hbound
    have hb' : aeval b f = 0 := by
      simpa only [ι, IsRoot.def, eval_map_algebraMap] using
        (mem_roots (map_ne_zero hf.ne_zero)).mp hb
    obtain ⟨σ, rfl⟩ := minpoly.exists_algEquiv_of_root'
      (Algebra.IsIntegral.isIntegral a).isAlgebraic hb'
    simpa only [norm_sub_rev] using ha σ
  have hlc : ‖(q.map ι).leadingCoeff‖ = ‖(f.natDegree.choose k : ℚ_[p])‖ := by
    rw [leadingCoeff_map_of_injective (RingHom.injective ι)]
    change ‖algebraMap ℚ_[p] (PadicAlgCl p)
      (hasseDeriv (f.natDegree - k) f).leadingCoeff‖ = _
    rw [monic_hasseDeriv_leadingCoeff f hf hkn, norm_algebraMap, norm_one, mul_one]
  refine ⟨b, hbdeg, ?_⟩
  rw [hqmdeg, hlc] at hnear
  exact hnear.trans (div_le_div_of_nonneg_right heval (norm_nonneg _))

/-- Passing to a nearby algebraic point increases displacement by at most its distance. -/
theorem padicGalois_displacement_nearby (a b : PadicAlgCl p) {r d : ℝ}
    (ha : ∀ σ : PadicGalois p, ‖σ a - a‖ ≤ r) (hab : ‖a - b‖ ≤ d) :
    ∀ σ : PadicGalois p, ‖σ b - b‖ ≤ max r d := by
  intro σ
  have he : σ b - b = σ (b - a) + (σ a - a) + (a - b) := by rw [map_sub]; ring
  have hn : ‖σ (b - a)‖ = ‖a - b‖ := by
    rw [(padicGalois_isometry p σ).norm_map_of_map_zero (map_zero _) _, norm_sub_rev]
  rw [he]
  apply (IsUltrametricDist.norm_add_le_max _ _).trans
  apply max_le
  · apply (IsUltrametricDist.norm_add_le_max _ _).trans
    rw [hn]
    exact max_le (hab.trans (le_max_right _ _)) ((ha σ).trans (le_max_left _ _))
  · exact hab.trans (le_max_right _ _)

end PadicHodgeTheory
