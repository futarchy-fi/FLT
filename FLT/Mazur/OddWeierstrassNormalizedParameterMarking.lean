/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassNormalizedMarking

/-!
# The original and normalized odd parameters retain every section

The actual faithful parameters expose their full markings and the projection
identities needed to compare them after arbitrary source base change.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonObj
namespace FLT.Mazur.OddWeierstrassParameter
open AuxiliaryLevel WeierstrassIntegralChart
open IntegralWeierstrassParameter (oddChartEquation oddChart_discriminant)
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (g : AuxiliarySectionRing →+* R)
  {T : Over (Spec (.of R))}
  (p : (Over.map (auxiliaryCoefficientBase g)).obj T ⟶ levelThree)

/-- All original labels on the actual original cubic. -/
irreducible_def auxiliaryOriginalParameterMarking :
    Labels 3 →* (T ⟶ (auxiliaryPullbackGroup g).X) :=
  markingOf (auxiliaryPullbackGroup g).X (Labels 3)
    (auxiliaryOriginalParameter g p ≫ faithfulInclusion (auxiliaryPullbackGroup g).X (Labels 3))

/-- All normalized labels on the actual normalized cubic. -/
irreducible_def auxiliaryNormalizedParameterMarking :
    Labels 3 →* (T ⟶ (auxiliaryNormalizedGroup g).X) :=
  markingOf (auxiliaryNormalizedGroup g).X (Labels 3)
    (auxiliaryNormalizedParameter g p ≫
      faithfulInclusion (auxiliaryNormalizedGroup g).X (Labels 3))

attribute [local irreducible] auxiliaryPullbackGroup auxiliaryNormalizedGroup

/-- Projection of every original label is the original universal scheme section. -/
theorem auxiliaryOriginalParameterMarking_fst (a : Labels 3) :
    (auxiliaryOriginalParameterMarking g p a).left ≫
      (auxiliaryCoefficientGroupIso g).hom.hom.hom.hom.left ≫
        pullback.fst universalGroup.hom (auxiliaryCoefficientBase g) =
          p.left ≫ (levelThreeMarking a).left := by
  rw [auxiliaryOriginalParameterMarking_def]
  change (auxiliaryOriginalParameter g p ≫
    faithfulInclusion (auxiliaryPullbackGroup g).X (Labels 3) ≫
      value (auxiliaryPullbackGroup g).X (Labels 3) a).left ≫ _ = _
  rw [auxiliaryOriginalParameter_def, cartesianGroupParameter_value]
  exact cartesianGroupMarking_projection _ _ _ _ _ _ _

/-- The normalized actual level point projects every normalized label without loss. -/
theorem auxiliaryNormalizedParameterMarking_fst (a : Labels 3) :
    (auxiliaryNormalizedParameterMarking g p a).left ≫
      (auxiliaryNormalizedCoefficientGroupIso g).hom.hom.hom.hom.left ≫
        pullback.fst universalGroup.hom (auxiliaryNormalizedCoefficientBase g) =
          (auxiliaryNormalizedLevelPoint g p).left ≫ (levelThreeMarking a).left := by
  rw [auxiliaryNormalizedParameterMarking_def]
  symm
  change (auxiliaryNormalizedLevelPoint g p ≫
    faithfulInclusion (integralCurveGroup oddChartEquation oddChart_discriminant).X (Labels 3) ≫
    value (integralCurveGroup oddChartEquation oddChart_discriminant).X (Labels 3) a).left = _
  rw [auxiliaryNormalizedLevelPoint_def, originalGroupParameter_value,
    originalGroupMarking_left]
  rfl

/-- Every normalized label is carried back to its actual original section. -/
theorem auxiliaryNormalizedParameterMarking_compare (a : Labels 3) :
    auxiliaryNormalizedParameterMarking g p a ≫
      (auxiliaryNormalizationGroupIso g).hom.hom.hom.hom =
        auxiliaryOriginalParameterMarking g p a := by
  have hn : auxiliaryNormalizedParameterMarking g p a =
      auxiliaryOriginalParameterMarking g p a ≫
        (auxiliaryNormalizationGroupIso g).inv.hom.hom.hom := by
    rw [auxiliaryNormalizedParameterMarking_def, auxiliaryOriginalParameterMarking_def]
    exact auxiliaryNormalizedParameter_value g p a
  have hi : (auxiliaryNormalizationGroupIso g).inv.hom.hom.hom ≫
      (auxiliaryNormalizationGroupIso g).hom.hom.hom.hom = 𝟙 _ :=
    congrArg (fun k ↦ k.hom.hom.hom) (auxiliaryNormalizationGroupIso g).inv_hom_id
  rw [hn, Category.assoc, hi, Category.comp_id]

end FLT.Mazur.OddWeierstrassParameter
