/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.PadicCyclotomicDegree
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval

/-! # The exact norm of a local cyclotomic uniformizer -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
open Polynomial
variable (p : ℕ) [hp : Fact p.Prime]

/-- All conjugate distances to a Q_p scalar are equal, so the norm of the
minimal-polynomial evaluation is the corresponding power of the distance. -/
theorem padic_minpoly_eval_norm (a : PadicAlgCl p) (c : ℚ_[p]) :
    ‖(minpoly ℚ_[p] a).eval c‖ =
      ‖a - algebraMap ℚ_[p] (PadicAlgCl p) c‖ ^ (minpoly ℚ_[p] a).natDegree := by
  let f := (minpoly ℚ_[p] a).map (algebraMap ℚ_[p] (PadicAlgCl p))
  have hf : f.Monic := (minpoly.monic (Algebra.IsIntegral.isIntegral a)).map _
  have hs := IsAlgClosed.splits f
  have hr : ∀ b ∈ f.roots,
      ‖algebraMap ℚ_[p] (PadicAlgCl p) c - b‖ =
        ‖a - algebraMap ℚ_[p] (PadicAlgCl p) c‖ := by
    intro b hb
    have hb' : aeval b (minpoly ℚ_[p] a) = 0 := by
      simpa only [f, IsRoot.def, eval_map_algebraMap] using (mem_roots hf.ne_zero).mp hb
    obtain ⟨σ, rfl⟩ := minpoly.exists_algEquiv_of_root'
      (Algebra.IsIntegral.isIntegral a).isAlgebraic hb'
    rw [norm_sub_rev]
    have he : σ a - algebraMap ℚ_[p] (PadicAlgCl p) c =
        σ (a - algebraMap ℚ_[p] (PadicAlgCl p) c) := by rw [map_sub, σ.commutes]
    rw [he]
    exact (padicGalois_isometry p σ).norm_map_of_map_zero (map_zero _) _
  have he : f.eval (algebraMap ℚ_[p] (PadicAlgCl p) c) =
      algebraMap ℚ_[p] (PadicAlgCl p) ((minpoly ℚ_[p] a).eval c) := by
    exact eval_map_apply _ _
  have hprod := hs.eval_eq_prod_roots_of_monic hf (algebraMap ℚ_[p] (PadicAlgCl p) c)
  have hnorm := congrArg norm hprod
  rw [he, norm_algebraMap, norm_one, mul_one] at hnorm
  have hnp : ‖(f.roots.map (fun b ↦ algebraMap ℚ_[p] (PadicAlgCl p) c - b)).prod‖ =
      (f.roots.map (fun b ↦ ‖algebraMap ℚ_[p] (PadicAlgCl p) c - b‖)).prod :=
    (f.roots.prod_hom' (normHom (α := PadicAlgCl p))
      (fun b ↦ algebraMap ℚ_[p] (PadicAlgCl p) c - b)).symm
  rw [hnorm, hnp]
  have hmap : f.roots.map (fun b ↦ ‖algebraMap ℚ_[p] (PadicAlgCl p) c - b‖) =
      f.roots.map (fun _ ↦ ‖a - algebraMap ℚ_[p] (PadicAlgCl p) c‖) :=
    Multiset.map_congr rfl hr
  rw [hmap, Multiset.map_const', Multiset.prod_replicate, ← hs.natDegree_eq_card_roots]
  simp only [f, natDegree_map]

/-- A primitive p^(s+1)-th root has the expected exact uniformizer norm, in power form. -/
theorem padicCyclotomic_sub_one_norm_pow (s : ℕ) (ζ : PadicAlgCl p)
    (hζ : IsPrimitiveRoot ζ (p ^ (s + 1))) :
    ‖ζ - 1‖ ^ (p ^ s * (p - 1)) = (p : ℝ)⁻¹ := by
  have he := padic_minpoly_eval_norm p ζ 1
  rw [padicCyclotomic_minpoly p s ζ hζ, eval_one_cyclotomic_prime_pow,
    Padic.norm_p, map_one, natDegree_cyclotomic,
    Nat.totient_prime_pow hp.out (by omega), Nat.add_sub_cancel] at he
  exact he.symm

end PadicHodgeTheory
