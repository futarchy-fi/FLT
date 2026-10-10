/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInfinityLaurentChart
public import FLT.Mazur.WeierstrassInfinityResidueBoundary
public import FLT.Mazur.WeierstrassDividedGlobalTensorGluing

/-!
# Full Laurent infinity gluing in the actual projective residue model

The entire normalized original Y-boundary is the cartesian intersection
of the Laurent infinity chart and the retained finite tensor model. Gluing
these opens recovers the complete original projective residue model.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (hdepth : 0 < depth) (j : ℕ) (hj : j ≤ n)
open WeierstrassIntegralChart
local notation "K" => ResidueField R
local notation "e" => infinityResidueBoundaryInclusion D hdepth
local notation "l" => infinityLaurentChart hπ data D hdepth j hj
local notation "r" => finiteLocalTensorEmbedding hπ data K j hj
local notation "bIso" => infinityResidueBoundaryIso D hdepth

/-- The full Laurent boundary as the original open in the finite residue model. -/
def infinityLaurentBoundary : Spec (.of (InfinityResidueBoundary D hdepth)) ⟶
    finiteTensorModel hπ data K j hj :=
  (bIso).hom ≫ finiteTensorYBoundary hπ data K j hj

instance infinityLaurentBoundary_isOpenImmersion :
    IsOpenImmersion (infinityLaurentBoundary hπ data D hdepth j hj) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- Its image is the entire original Y-boundary, without selecting a component. -/
theorem infinityLaurentBoundary_range :
    Set.range (infinityLaurentBoundary hπ data D hdepth j hj) =
      Set.range (finiteTensorYBoundary hπ data K j hj) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(bIso).hom x, rfl⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := (bIso).hom.homeomorph.surjective x
    exact ⟨y, congrArg (finiteTensorYBoundary hπ data K j hj) hy⟩

/-- The original global overlap equality holds on the entire normalized boundary. -/
@[reassoc] theorem infinityLaurent_overlap :
    e ≫ l = infinityLaurentBoundary hπ data D hdepth j hj ≫ r := by
  rw [infinityLaurentChart, ← Category.assoc, ← infinityResidueBoundaryIso_inclusion,
    Category.assoc, finiteGlobalTensor_overlap, infinityLaurentBoundary, Category.assoc]

/-- No additional identifications occur between infinity and the finite tensor model. -/
theorem infinityLaurent_overlap_preimage :
    r ⁻¹' Set.range l = Set.range (infinityLaurentBoundary hπ data D hdepth j hj) := by
  rw [infinityLaurentChart_range, infinityLaurentBoundary_range]
  exact finiteGlobalTensor_overlap_preimage hπ data K j hj

/-- The full normalized boundary is the actual cartesian intersection. -/
theorem infinityLaurent_overlap_isPullback :
    IsPullback e (infinityLaurentBoundary hπ data D hdepth j hj) l r := by
  apply IsOpenImmersion.isPullback _ _ _ _ (infinityLaurent_overlap hπ data D hdepth j hj).symm
  exact TopologicalSpace.Opens.ext (infinityLaurent_overlap_preimage hπ data D hdepth j hj)

/-- The Laurent infinity chart and the whole finite model cover the original residue model. -/
theorem infinityLaurent_charts_cover (z : finiteGlobalTensorModel hπ data K j hj) :
    (∃ x, l x = z) ∨ ∃ x, r x = z := by
  change z ∈ Set.range l ∪ Set.range r
  rw [infinityLaurentChart_range]
  exact finiteGlobalTensor_charts_cover hπ data K j hj z

/-- Gluing the entire Laurent boundary recovers the actual projective residue model. -/
def infinityLaurentGluingIso :
    pushout e (infinityLaurentBoundary hπ data D hdepth j hj) ≅
      finiteGlobalTensorModel hπ data K j hj :=
  SchemeOpenPushout.coverIso _ _ _ _ (infinityLaurent_overlap_isPullback hπ data D hdepth j hj)
    (infinityLaurent_charts_cover hπ data D hdepth j hj)

/-- The normalized gluing comparison retains the original infinity inclusion. -/
@[reassoc] theorem infinityLaurentGluingIso_infinity :
    pushout.inl e (infinityLaurentBoundary hπ data D hdepth j hj) ≫
      (infinityLaurentGluingIso hπ data D hdepth j hj).hom = l :=
  SchemeOpenPushout.inl_coverIso _ _ _ _ _ _

/-- The normalized gluing comparison retains the entire original finite tensor model. -/
@[reassoc] theorem infinityLaurentGluingIso_local :
    pushout.inr e (infinityLaurentBoundary hπ data D hdepth j hj) ≫
      (infinityLaurentGluingIso hπ data D hdepth j hj).hom = r :=
  SchemeOpenPushout.inr_coverIso _ _ _ _ _ _

end FLT.Mazur.WeierstrassDividedDepth
