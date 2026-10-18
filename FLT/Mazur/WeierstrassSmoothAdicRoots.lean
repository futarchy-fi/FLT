/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassSmoothAdicReduction

/-!
# Constructing compatible roots at every actual adic order

Starting with a prescribed root at the first positive order, the unique
square-zero lifting theorem constructs the whole compatible root tower.
Each root has exactly the power prescribed by the original full-base section.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonObj

namespace FLT.Mazur.WeierstrassSmoothAdicRoots

open WeierstrassIntegralChart WeierstrassSmoothAdicReduction

variable {R : Type} [CommRing R] [IsLocalRing R]
  (W : WeierstrassCurve R) (I : Ideal R) (hI : I ≠ ⊤)
  (n : ℕ) (hn : IsUnit (n : R))
  (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R R))) ⟶
    (integralSmoothGroup W).X)
  (b : Points W I 0) (hb : b ^ n = sectionReduction W I 0 x)

/-- A root at one order, retaining the exact reduction of the original full-base point. -/
def Root (m : ℕ) := {y : Points W I m // y ^ n = sectionReduction W I m x}

/-- Construct the next root over the actual adjacent coefficient extension. -/
def next (m : ℕ) (y : Root W I n x m) : Root W I n x (m + 1) := by
  have hy : y.val ^ n = reduction W I m (sectionReduction W I (m + 1) x) := by
    rw [reduction_sectionReduction]
    exact y.property
  let z := existsUnique_next_root W I hI n hn m (sectionReduction W I (m + 1) x) y.val hy
  exact ⟨z.choose, z.choose_spec.1.2⟩

/-- The constructed next root retains the entire preceding relative scheme map. -/
theorem reduction_next (m : ℕ) (y : Root W I n x m) :
    reduction W I m (next W I hI n hn x m y).val = y.val := by
  exact (existsUnique_next_root W I hI n hn m (sectionReduction W I (m + 1) x) y.val
    (by rw [reduction_sectionReduction]; exact y.property)).choose_spec.1.1

/-- Recursively construct roots at every order, starting at precisely the prescribed root. -/
def stage : (m : ℕ) → Root W I n x m
  | 0 => ⟨b, hb⟩
  | m + 1 => next W I hI n hn x m (stage m)

/-- The constructed zeroth root is the prescribed original relative point. -/
theorem stage_zero : (stage W I hI n hn x b hb 0).val = b := rfl

/-- The original full-base point is exactly the power of every constructed finite root. -/
theorem stage_pow (m : ℕ) :
    (stage W I hI n hn x b hb m).val ^ n = sectionReduction W I m x :=
  (stage W I hI n hn x b hb m).property

/-- Adjacent roots agree under the original coefficient restrictions. -/
theorem reduction_stage (m : ℕ) :
    reduction W I m (stage W I hI n hn x b hb (m + 1)).val =
      (stage W I hI n hn x b hb m).val :=
  reduction_next W I hI n hn x m (stage W I hI n hn x b hb m)

/-- Any compatible tower of roots with the prescribed first root equals the constructed tower. -/
theorem stage_unique (s : ∀ m, Points W I m)
    (hs0 : s 0 = b) (hspow : ∀ m, s m ^ n = sectionReduction W I m x)
    (hs : ∀ m, reduction W I m (s (m + 1)) = s m) (m : ℕ) :
    s m = (stage W I hI n hn x b hb m).val := by
  induction m with
  | zero => exact hs0
  | succ m ih =>
    have hy : (stage W I hI n hn x b hb m).val ^ n =
        reduction W I m (sectionReduction W I (m + 1) x) := by
      rw [reduction_sectionReduction, stage_pow]
    have hu := existsUnique_next_root W I hI n hn m
      (sectionReduction W I (m + 1) x) (stage W I hI n hn x b hb m).val hy
    exact hu.unique ⟨(hs m).trans ih, hspow (m + 1)⟩
      ⟨reduction_stage W I hI n hn x b hb m, stage_pow W I hI n hn x b hb (m + 1)⟩

end FLT.Mazur.WeierstrassSmoothAdicRoots
