/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset
public import Mathlib.Data.Finset.Max

/-! # A nearby root from the product of root distances -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
open Polynomial
variable {K : Type*} [NormedField K]

/-- A split polynomial of positive degree has a root bounded by its normalized evaluation.
The power formulation also covers a zero evaluation without exceptional real-power conventions. -/
theorem polynomial_exists_nearby_root (f : K[X]) (hsplit : f.Splits)
    (hdeg : 0 < f.natDegree) (a : K) :
    ∃ b ∈ f.roots, ‖a - b‖ ^ f.natDegree ≤ ‖f.eval a‖ / ‖f.leadingCoeff‖ := by
  classical
  have hf : f ≠ 0 := ne_zero_of_natDegree_gt hdeg
  have hc := hsplit.natDegree_eq_card_roots
  have hn : f.roots.toFinset.Nonempty := by
    obtain ⟨b, hb⟩ := Multiset.card_pos_iff_exists_mem.mp (hc ▸ hdeg)
    exact ⟨b, Multiset.mem_toFinset.mpr hb⟩
  obtain ⟨b, hb, hmin⟩ := Finset.exists_min_image f.roots.toFinset (fun b ↦ ‖a - b‖) hn
  refine ⟨b, Multiset.mem_toFinset.mp hb, ?_⟩
  have hprod := Multiset.prod_map_le_prod_map₀ (s := f.roots)
    (fun _ ↦ ‖a - b‖) (fun c ↦ ‖a - c‖)
    (fun _ _ ↦ norm_nonneg _) (fun c hc ↦ hmin c (Multiset.mem_toFinset.mpr hc))
  have he : (f.roots.map (fun c ↦ ‖a - c‖)).prod =
      ‖f.eval a‖ / ‖f.leadingCoeff‖ := by
    rw [hsplit.eval_eq_prod_roots, norm_mul, mul_div_cancel_left₀ _
      (norm_ne_zero_iff.mpr (leadingCoeff_ne_zero.mpr hf))]
    exact f.roots.prod_hom' (normHom (α := K)) (fun c ↦ a - c)
  simpa only [Multiset.map_const', Multiset.prod_replicate, ← hc, he] using hprod

end PadicHodgeTheory
