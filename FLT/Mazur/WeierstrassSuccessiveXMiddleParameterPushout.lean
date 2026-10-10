/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleLocalizedBranchMaps
public import FLT.Mazur.WeierstrassModificationXConicParameterOrigin

/-!
# The actual conic parameter and horizontal line pinch to the full middle node

The normalization sources are the original parameter schemes. Their origins,
branch maps and arbitrary-target universal property keep the divided constant.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits Polynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
universe u
variable {K : Type u} [Field K] (c : K)
local notation "s" => middleNodePairDenominator c
local notation "hs" => middleNodePairDenominator_value c
local notation "P" => ConicParameterOpen c
local notation "L" => MiddleNodeOpen c

/-- The original conic parameter scheme is the first localized normalization branch. -/
def middleConicBranchSourceIso : Spec (.of P) ≅
    Spec (.of (Localization.Away (PolygonNodeEqualizer.first s))) :=
  Scheme.Spec.mapIso (middleLocalizedConicParameterEquiv c).toCommRingCatIso.op

/-- The original affine line is the entire second normalization branch. -/
def middleLineBranchSourceIso : ProjectiveLine.chart K ≅
    Spec (.of (Localization.Away (PolygonNodeEqualizer.second s))) :=
  Scheme.Spec.mapIso (middleLocalizedLineEquiv c).toCommRingCatIso.op

/-- The original conic parameter open embedded in the full localized node. -/
def middleParameterConicBranch : Spec (.of P) ⟶ Spec (.of L) :=
  Spec.map (CommRingCat.ofHom (middleLocalizedConicRestriction c).toRingHom)

/-- The original entire horizontal line embedded in the full localized node. -/
def middleParameterLineBranch : ProjectiveLine.chart K ⟶ Spec (.of L) :=
  Spec.map (CommRingCat.ofHom (middleLocalizedLineRestriction c).toRingHom)

/-- The original conic restriction is the pushout's first branch after source comparison. -/
@[reassoc] theorem middleConicBranchSourceIso_branch :
    (middleConicBranchSourceIso c).hom ≫ middleNodeLocalizedFirstBranch c =
      middleParameterConicBranch c := by
  rw [middleNodeLocalizedFirstBranch_eq_spec]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

/-- The original horizontal restriction is the pushout's second branch. -/
@[reassoc] theorem middleLineBranchSourceIso_branch :
    (middleLineBranchSourceIso c).hom ≫ middleNodeLocalizedSecondBranch c =
      middleParameterLineBranch c := by
  rw [middleNodeLocalizedSecondBranch_eq_spec]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

/-- The source comparison preserves the actual conic parameter origin. -/
@[reassoc] theorem middleConicBranchSourceIso_origin :
    Spec.map (CommRingCat.ofHom (conicParameterOrigin c).toRingHom) ≫
      (middleConicBranchSourceIso c).hom = NodeLocalDescent.firstOrigin K s hs := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply IsLocalization.ringHom_ext (Submonoid.powers (PolygonNodeEqualizer.first s))
  apply RingHom.ext
  intro p
  change conicParameterOrigin c
    (middleLocalizedConicParameterEquiv c (algebraMap K[X] _ p)) = _
  rw [middleLocalizedConicParameterEquiv_base, conicParameterOrigin_base]
  exact (NodeLocalizedEqualizer.evaluation_algebraMap _ _
    (NodeLocalizedEqualizer.first_value s hs) p).symm

/-- The source comparison preserves the actual horizontal origin. -/
@[reassoc] theorem middleLineBranchSourceIso_origin :
    ProjectiveLine.chartZero K ≫ (middleLineBranchSourceIso c).hom =
      NodeLocalDescent.secondOrigin K s hs := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply IsLocalization.ringHom_ext (Submonoid.powers (PolygonNodeEqualizer.second s))
  apply RingHom.ext
  intro p
  change (middleLocalizedLineEquiv c (algebraMap K[X] _ p)).eval 0 = _
  rw [middleLocalizedLineEquiv_base]
  exact (NodeLocalizedEqualizer.evaluation_algebraMap _ _
    (NodeLocalizedEqualizer.second_value s hs) p).symm

/-- The original conic parameter and entire horizontal line form a scheme pushout. -/
theorem middleParameterBranches_isPushout :
    IsPushout (Spec.map (CommRingCat.ofHom (conicParameterOrigin c).toRingHom))
      (ProjectiveLine.chartZero K) (middleParameterConicBranch c) (middleParameterLineBranch c) :=
  (middleNodeLocalizedBranches_isPushout c).of_iso (Iso.refl _)
    (middleConicBranchSourceIso c).symm (middleLineBranchSourceIso c).symm (Iso.refl _)
    (by simp [← middleConicBranchSourceIso_origin c])
    (by simp [← middleLineBranchSourceIso_origin c])
    (by simp [← middleConicBranchSourceIso_branch c])
    (by simp [← middleLineBranchSourceIso_branch c])

/-- The conic origin is the original attachment section. -/
@[reassoc] theorem middleParameterConicBranch_origin :
    Spec.map (CommRingCat.ofHom (conicParameterOrigin c).toRingHom) ≫
      middleParameterConicBranch c =
        Spec.map (CommRingCat.ofHom (middleNodeOrigin c).toRingHom) := by
  rw [← middleConicBranchSourceIso_branch, middleConicBranchSourceIso_origin_assoc,
    middleNodeLocalizedFirstBranch_origin]

/-- The horizontal origin is the same original attachment section. -/
@[reassoc] theorem middleParameterLineBranch_origin :
    ProjectiveLine.chartZero K ≫ middleParameterLineBranch c =
      Spec.map (CommRingCat.ofHom (middleNodeOrigin c).toRingHom) :=
  (middleParameterBranches_isPushout c).w.symm.trans (middleParameterConicBranch_origin c)

end FLT.Mazur.WeierstrassSuccessiveX
