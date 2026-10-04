/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.PadicRelativeGalois
public import FLT.PadicHodgeTheory.PadicHasseApproximation
public import FLT.PadicHodgeTheory.PolynomialNearbyRoot
public import FLT.PadicHodgeTheory.UltrametricPolynomialCoefficients

/-! # Relative lower-degree approximants from actual Hasse derivatives -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
open Polynomial
variable (p : ℕ) [Fact p.Prime] (E : IntermediateField ℚ_[p] (PadicAlgCl p))

/-- Hasse derivatives produce smaller-degree points, with the exact binomial loss exposed. -/
theorem padicRelativeHasse_exists_approximation (a : PadicAlgCl p) {r : ℝ} (hr : 0 ≤ r)
    (ha : ∀ σ : Gal(PadicAlgCl p/E), ‖σ a - a‖ ≤ r) {k : ℕ} (hk : 0 < k)
    (hkn : k ≤ (minpoly E a).natDegree) :
    ∃ b : PadicAlgCl p, (minpoly E b).natDegree ≤ k ∧
      ‖a - b‖ ^ k ≤ r ^ k / ‖((minpoly E a).natDegree.choose k : ℚ_[p])‖ := by
  let f := minpoly E a
  let q := hasseDeriv (f.natDegree - k) f
  let ι := algebraMap E (PadicAlgCl p)
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
  have hbdeg : (minpoly E b).natDegree ≤ k := by
    rw [← hqdeg]
    exact natDegree_le_natDegree (minpoly.degree_le_of_ne_zero E b hq hbroot)
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
    change ‖algebraMap E (PadicAlgCl p)
      (hasseDeriv (f.natDegree - k) f).leadingCoeff‖ = _
    rw [monic_hasseDeriv_leadingCoeff f hf hkn, map_natCast]
    rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) (f.natDegree.choose k),
      norm_algebraMap, norm_one, mul_one]
  refine ⟨b, hbdeg, ?_⟩
  rw [hqmdeg, hlc] at hnear
  exact hnear.trans (div_le_div_of_nonneg_right heval (norm_nonneg _))

end PadicHodgeTheory
