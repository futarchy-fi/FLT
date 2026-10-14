/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationMonicSeedOpen
public import FLT.Mazur.SchemeRelationMonicSeedSelection

/-!
# Genuine affine open selections through every propagated source point

Take an affine open of the constructed branch, whose map to the original
source is now proved to be an open immersion. Each selection keeps its
original ground base, is etale over the coefficient target, and has the
complete original relation as its kernel.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationMonicSeedKernel
set_option backward.isDefEq.respectTransparency false
variable {S T Z : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) (w : A.left ⟶ T)
  (h : p.left ≫ w = q.left ≫ w) (a : Z ⟶ A.left)
local notation "B" => (pullback q.left a : Scheme)
local notation "b" => SchemeRelationEtaleBranchPropagation.branch p.left q.left a
variable (z : (pullback q.left a : Scheme))

/-- The affine member of the branch cover through the specified point. -/
def affineSource : Over S :=
  Over.mk ((B).affineOpenCover.f ((B).affineOpenCover.idx z) ≫ b ≫ A.hom)

/-- The actual affine-open map into the constructed branch. -/
def affineToBranch : (affineSource (p := p) a z).left ⟶ B :=
  (B).affineOpenCover.f ((B).affineOpenCover.idx z)

/-- The selected source is a scheme over the unchanged original ground base. -/
def affineMap : affineSource (p := p) a z ⟶ A :=
  Over.homMk (affineToBranch (p := p) a z ≫ b)

instance affineSource_isAffine : IsAffine (affineSource (p := p) a z).left :=
  inferInstanceAs (IsAffine (Spec ((B).affineOpenCover.X ((B).affineOpenCover.idx z))))

instance affineToBranch_isOpenImmersion : IsOpenImmersion (affineToBranch (p := p) a z) :=
  inferInstanceAs (IsOpenImmersion ((B).affineOpenCover.f ((B).affineOpenCover.idx z)))

/-- An actual point in the affine selection, with no change to its original source image. -/
def affinePoint : (affineSource (p := p) a z).left := ((B).affineOpenCover.covers z).choose

/-- The selected affine neighborhood contains the requested branch point. -/
theorem affinePoint_toBranch : affineToBranch (p := p) a z (affinePoint (p := p) a z) = z :=
  ((B).affineOpenCover.covers z).choose_spec

/-- Every represented source point survives the actual affine-open selection. -/
theorem affinePoint_original : (affineMap (p := p) a z).left (affinePoint (p := p) a z) = b z :=
  congrArg b (affinePoint_toBranch (p := p) a z)

variable [Mono (a ≫ w)] [Mono (pullback.lift p.left q.left h)]

include h in
/-- These are open selections of the original source, not only etale neighborhoods. -/
theorem affineMap_isOpenImmersion [Etale p.left] [Etale a] :
    IsOpenImmersion (affineMap (p := p) a z).left := by
  let _ := branch_isOpenImmersion w h a
  exact inferInstanceAs (IsOpenImmersion (affineToBranch (p := p) a z ≫ b))

include h in
omit [Mono (a ≫ w)] [Mono (pullback.lift p.left q.left h)] in
/-- The entire affine source remains etale over the original coefficient target. -/
theorem affineMap_target_etale [Etale q.left] [Etale (a ≫ w)] :
    Etale ((affineMap (p := p) a z).left ≫ w) := by
  let _ := SchemeRelationEtaleBranchPropagation.branch_target_etale p.left q.left w h a
  change Etale ((affineToBranch (p := p) a z ≫ b) ≫ w)
  rw [Category.assoc]
  infer_instance

include e h in
/-- The full original relation on every affine selection is its coefficient kernel. -/
theorem affineMap_isPullback : IsPullback
    (SchemeRelationRestriction.fst p.left q.left (affineMap (p := p) a z).left)
    (SchemeRelationRestriction.snd p.left q.left (affineMap (p := p) a z).left)
    ((affineMap (p := p) a z).left ≫ w) ((affineMap (p := p) a z).left ≫ w) :=
  selection_isPullback e w h a _ (affineToBranch (p := p) a z) rfl

end FLT.Mazur.SchemeRelationMonicSeedKernel
