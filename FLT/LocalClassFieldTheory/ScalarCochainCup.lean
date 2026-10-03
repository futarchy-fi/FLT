/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

/-!
# Right scalar cups and their differential

A one-cochain can be cupped on the right with a scalar cochain of any degree.
The differential formula is the Leibniz identity needed to compute the two
successive connecting maps of a two-extension.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable {k G : Type} [CommRing k] [Group G] (M : Rep k G)

/-- Right scalar cup with a one-cochain. -/
def scalarCupOne (f : G → M) {n : ℕ} (z : (Fin n → G) → k) :
    (Fin (n + 1) → G) → M := fun v => z (fun i => v i.succ) • f (v 0)

/-- Contracting at the first position removes the first two entries from the tail. -/
theorem contractZero_tail {n : ℕ} (v : Fin (n + 2) → G) :
    (fun i : Fin n => Fin.contractNth 0 (· * ·) v i.succ) =
      (fun i => v i.succ.succ) := by
  funext i
  simp [Fin.contractNth]

/-- A contraction after the first position leaves the first entry unchanged. -/
theorem contractSucc_head {n : ℕ} (v : Fin (n + 2) → G) (j : Fin (n + 1)) :
    Fin.contractNth j.succ (· * ·) v 0 = v 0 := by
  simp [Fin.contractNth]

/-- Taking the tail commutes with contraction after the first position. -/
theorem contractSucc_tail {n : ℕ} (v : Fin (n + 2) → G) (j : Fin (n + 1)) :
    (fun i : Fin n => Fin.contractNth j.succ (· * ·) v i.succ) =
      Fin.contractNth j (· * ·) (fun i => v i.succ) := by
  funext i
  simp [Fin.contractNth]

/-- The scalar cup satisfies the degree-one Leibniz formula in every degree. -/
theorem scalarCupOne_d (f : G → M) {n : ℕ} (z : (Fin n → G) → k)
    (v : Fin (n + 2) → G) :
    inhomogeneousCochains.d M (n + 1) (scalarCupOne M f z) v =
      z (fun i => v i.succ.succ) • (d₁₂ M f (v 0, v 1)) -
        (inhomogeneousCochains.d (Rep.trivial k G k) n z (fun i => v i.succ)) • f (v 0) := by
  rw [inhomogeneousCochains.d_hom_apply, Fin.sum_univ_succ]
  simp only [scalarCupOne, contractZero_tail, contractSucc_head, contractSucc_tail]
  simp only [Fin.contractNth, Fin.val_zero, lt_self_iff_false, ↓reduceIte,
    Fin.castSucc_zero, Fin.succ_zero_eq_one]
  rw [inhomogeneousCochains.d_hom_apply]
  change _ = _ - (z (fun i => v i.succ.succ) +
    ∑ j : Fin (n + 1), (-1 : k) ^ (j.val + 1) •
      z (Fin.contractNth j (· * ·) (fun i => v i.succ))) • f (v 0)
  simp only [d₁₂_hom_apply, map_smul, smul_sub, smul_add, add_smul, Finset.sum_smul,
    smul_smul, Fin.val_succ, pow_succ, mul_neg, mul_one, neg_mul, neg_smul,
    Finset.sum_neg_distrib]
  simp only [smul_eq_mul, pow_zero, one_mul]
  abel

end LocalClassFieldTheory
