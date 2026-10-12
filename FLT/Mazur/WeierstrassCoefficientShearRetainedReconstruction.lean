/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections
import all FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections

/-!
# Reconstruction of both indexed retained tensor charts

The complete equation gluing reconstructs each original tensor chart as a
morphism. In particular, both adjacent charts have the same common target.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (r : S)

/-- Reconstruction identifies the entire retained tensor chart with its original map. -/
@[reassoc] theorem coefficientShearRetainedTensorChart_original
    (j : ℕ) (hj : j + 1 ≤ n) (m : ℕ) (hm : j + 1 + m ≤ n) :
    coefficientShearRetainedTensorChart hπ data S r (j + 1 + m) hm ⟨j, by omega⟩ ≫
      (coefficientShearGluedIso hπ data S r (j + 1 + m) hm).hom =
        olderGlobalTensorChart hπ data S j hj m hm := by
  rw [coefficientShearRetainedTensorChart, Category.assoc, coefficientShearGluedIso_chart]
  change _ ≫ retainedCoefficientShearChart hπ data S r (j + 1 + m) hm j (by omega) = _
  rw [retainedCoefficientShearChart_original hπ data S r j hj m hm,
    olderGlobalCoefficientShearChart, Iso.inv_hom_id_assoc]

/-- Both old target-index spellings reconstruct the same original tensor morphism. -/
theorem coefficientShearRetainedTensorChart_original_heq
    (t : ℕ) (ht : t ≤ n) (j : ℕ) (hj : j + 1 ≤ t)
    (m : ℕ) (hm : j + 1 + m ≤ n) (he : t = j + 1 + m) :
    HEq (coefficientShearRetainedTensorChart hπ data S r t ht ⟨j, by omega⟩ ≫
      (coefficientShearGluedIso hπ data S r t ht).hom)
        (olderGlobalTensorChart hπ data S j (by omega) m hm) := by
  subst t
  exact heq_of_eq (coefficientShearRetainedTensorChart_original hπ data S r j
    (by omega) m hm)

variable (j : ℕ) (hj : j + 1 ≤ n) (hjNext : j + 2 ≤ n)
  (m : ℕ) (hm : j + 2 + m ≤ n)

/-- The older member reconstructs its actual chart at the common later depth. -/
@[reassoc] theorem coefficientShearRetainedTensorChart_adjacent_old :
    coefficientShearRetainedTensorChart hπ data S r (j + 2 + m) hm ⟨j, by omega⟩ ≫
      (coefficientShearGluedIso hπ data S r (j + 2 + m) hm).hom =
        adjacentRetainedOldGlobalTensorChart hπ data S j hj m hm := by
  apply eq_of_heq
  exact (coefficientShearRetainedTensorChart_original_heq hπ data S r
    (j + 2 + m) hm j (by omega) (m + 1) (by omega) (by omega)).trans
      (adjacentRetainedOldGlobalTensorChart_heq hπ data S j hj m hm)

/-- The next member reconstructs its actual chart at that same common depth. -/
@[reassoc] theorem coefficientShearRetainedTensorChart_adjacent_next :
    coefficientShearRetainedTensorChart hπ data S r (j + 2 + m) hm ⟨j + 1, by omega⟩ ≫
      (coefficientShearGluedIso hπ data S r (j + 2 + m) hm).hom =
        olderGlobalTensorChart hπ data S (j + 1) hjNext m hm :=
  coefficientShearRetainedTensorChart_original hπ data S r (j + 1) hjNext m hm

end FLT.Mazur.WeierstrassDividedDepth
