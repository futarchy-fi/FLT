/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicProductOriginalSubgroupLocus
public import FLT.Mazur.CyclicCharacteristicProductSubgroupInclusion
public import FLT.Mazur.OverDirectedMonoGluing

/-!
# The glued subgroup parameter scheme is the original global comparison locus

Both closed subobjects have the same concrete affine charts. Their local
identifications descend to an isomorphism over the full comparison scheme.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b c : Bool)
local notation "C" => Scheme.Cover.RelativeGluingData.cover (productComparisonGluing n b c)
local notation "i" => productSubgroupInclusion n b c
local notation "j" => productOriginalSubgroupInclusion n b c
variable (U : (normalizedProduct n b c).affineOpens)
local notation "z" => affineSubgroupInclusion n b c
  (productOpenLeft n b c U) (productOpenRight n b c U)

/-- The concrete subgroup chart is the actual slice pullback of the glued closed subobject. -/
def productSubgroupChartOverIso : Over.mk z ≅ (Over.pullback ((C).f U)).obj (Over.mk i) :=
  Over.isoMk (productSubgroupInclusion_isPullback n b c U).flip.isoPullback
    (productSubgroupInclusion_isPullback n b c U).flip.isoPullback_hom_snd

/-- The same chart is the actual slice pullback of the original global subgroup condition. -/
def productOriginalSubgroupChartOverIso :
    Over.mk z ≅ (Over.pullback ((C).f U)).obj (Over.mk j) :=
  Over.isoMk (productOriginalSubgroupChartIso n b c U ≪≫ pullbackSymmetry _ _) (by
    change ((productOriginalSubgroupChartIso n b c U).hom ≫
      (pullbackSymmetry _ _).hom) ≫ pullback.snd _ _ = z
    rw [Category.assoc, pullbackSymmetry_hom_comp_snd, productOriginalSubgroupChartIso_fst])

/-- The two global subgroup parameter schemes are isomorphic over their original parameter base. -/
def productSubgroupLocusOverIso : Over.mk i ≅ Over.mk j := by
  let _ : Mono (Over.mk i).hom := inferInstanceAs (Mono (productSubgroupInclusion n b c))
  let _ : Mono (Over.mk j).hom := inferInstanceAs (Mono (productOriginalSubgroupInclusion n b c))
  exact OverDirectedCoverGluing.glueMonoIso C (X := Over.mk i) (Y := Over.mk j) (fun U ↦
    (productSubgroupChartOverIso n b c U).symm ≪≫ productOriginalSubgroupChartOverIso n b c U)

/-- The actual glued subgroup scheme is the closed locus of the full global universal comparison. -/
def productSubgroupLocusIso : productSubgroupScheme n b c ≅ productOriginalSubgroupLocus n b c :=
  (Over.forget _).mapIso (productSubgroupLocusOverIso n b c)

/-- The identification preserves the exact original closed immersion. -/
@[reassoc] theorem productSubgroupLocusIso_inclusion :
    (productSubgroupLocusIso n b c).hom ≫ j = i :=
  (productSubgroupLocusOverIso n b c).hom.w

end FLT.Mazur.CyclicCharacteristicAtlas
