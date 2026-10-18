/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassSmoothCompleteSections

/-!
# Prescribed roots over the original complete local coefficient ring

Reconstruction of the actual adic root tower gives a root of the original
full-base point. Its first reduction is prescribed, and it is unique.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonObj
namespace FLT.Mazur.WeierstrassSmoothCompleteRoots

open WeierstrassSmoothAdicReduction WeierstrassSmoothAdicRoots
  WeierstrassSmoothCompleteSections
variable {R : Type} [CommRing R] [IsLocalRing R]
  (W : WeierstrassCurve R) (I : Ideal R) (hI : I ≠ ⊤) [IsAdicComplete I R]
  (n : ℕ) (hn : IsUnit (n : R)) (x : Sections W)
  (b : Points W I 0) (hb : b ^ n = sectionReduction W I 0 x)

/-- The root is an actual full-base smooth-group section. -/
def root : Sections W :=
  reconstruct W I hI (fun m ↦ (stage W I hI n hn x b hb m).val)
    (reduction_stage W I hI n hn x b hb)

/-- Every finite restriction of the complete root is the constructed root at that order. -/
theorem reduction_root (m : ℕ) :
    sectionReduction W I m (root W I hI n hn x b hb) =
      (stage W I hI n hn x b hb m).val := reduction_reconstruct W I hI _ _ m

/-- The complete root has exactly the original prescribed power. -/
theorem root_pow : root W I hI n hn x b hb ^ n = x := by
  apply section_ext W I hI
  intro m
  rw [map_pow, reduction_root, stage_pow]

/-- The complete root retains the prescribed first relative scheme map. -/
theorem root_reduction : sectionReduction W I 0 (root W I hI n hn x b hb) = b := by
  rw [reduction_root, stage_zero]

/-- The prescribed power and first reduction determine the full complete-base section. -/
theorem root_unique (y : Sections W) (hy : y ^ n = x)
    (hyb : sectionReduction W I 0 y = b) : y = root W I hI n hn x b hb := by
  apply section_ext W I hI
  intro m
  rw [reduction_root]
  apply stage_unique W I hI n hn x b hb (fun k ↦ sectionReduction W I k y) hyb
  · intro k
    rw [← map_pow, hy]
  · intro k
    exact reduction_sectionReduction W I k y

include hI hn hb in
/-- Every prescribed first-order power root lifts uniquely to the original complete base. -/
theorem existsUnique_root : ∃! y : Sections W, sectionReduction W I 0 y = b ∧ y ^ n = x :=
  ⟨root W I hI n hn x b hb,
    ⟨root_reduction W I hI n hn x b hb, root_pow W I hI n hn x b hb⟩,
    fun _ hy ↦ root_unique W I hI n hn x b hb _ hy.2 hy.1⟩

include hI hn in
/-- Unit-index powers are bijective on the entire first-reduction kernel. -/
theorem kernel_pow_bijective :
    Function.Bijective (fun z : (sectionReduction W I 0).ker ↦ z ^ n) := by
  constructor
  · intro a b hab
    apply Subtype.ext
    have ha : (a.val) ^ n = (b.val) ^ n := congrArg Subtype.val hab
    have hred : (1 : Points W I 0) ^ n = sectionReduction W I 0 (b.val ^ n) := by
      rw [map_pow, b.property, one_pow]
    exact (root_unique W I hI n hn (b.val ^ n) 1 hred a.val ha a.property).trans
      (root_unique W I hI n hn (b.val ^ n) 1 hred b.val rfl b.property).symm
  · intro x
    have hx : (1 : Points W I 0) ^ n = sectionReduction W I 0 x.val := by
      rw [one_pow, x.property]
    refine ⟨⟨root W I hI n hn x.val 1 hx, root_reduction W I hI n hn x.val 1 hx⟩, ?_⟩
    exact Subtype.ext (root_pow W I hI n hn x.val 1 hx)

end FLT.Mazur.WeierstrassSmoothCompleteRoots
