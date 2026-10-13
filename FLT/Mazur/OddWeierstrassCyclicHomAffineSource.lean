/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassNormalizedFamilyPoint
public import FLT.Mazur.OddWeierstrassNormalizedCyclicSource

/-!
# Affine original cyclic sources and their auxiliary coefficient cubics

The global-functions map of the actual auxiliary point identifies its pulled
cubic with the entire cyclic source, without an affineness assumption on the
auxiliary parameter scheme.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OddWeierstrassParameter
open GeneralizedEllipticCurve WeierstrassIntegralChart
open IntegralWeierstrassParameter (oddChartEquation oddChart_discriminant)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (n : ℕ) [NeZero n]
  (f : Spec (.of R) ⟶ (cyclicHomAuxiliaryScheme n).left)
local notation "a" => cyclicHomAuxiliaryPoint n f
local notation "g" => auxiliaryPointSections a
local notation "G" => integralCurveGroup oddChartEquation oddChart_discriminant

/-- The actual affine source group is its original auxiliary coefficient cubic. -/
irreducible_def cyclicHomAffineSourceGroupIso : auxiliaryPullbackGroup g ≅
    (Over.pullback (a ≫ levelThree.hom)).mapCommGrp.obj G :=
  auxiliaryCoefficientGroupIso g ≪≫
    GroupSchemeBaseChange.congrIso (auxiliaryPointSections_base a) G

/-- This group comparison retains the original coefficient projection. -/
@[reassoc] theorem cyclicHomAffineSourceGroupIso_fst :
    (cyclicHomAffineSourceGroupIso n f).hom.hom.hom.hom.left ≫
      pullback.fst universalGroup.hom (a ≫ levelThree.hom) =
        (auxiliaryCoefficientGroupIso g).hom.hom.hom.hom.left ≫
          pullback.fst universalGroup.hom (auxiliaryCoefficientBase g) := by
  rw [cyclicHomAffineSourceGroupIso_def]
  change (_ ≫ _) ≫ _ = _
  exact (Category.assoc _ _ _).trans
    (congrArg (fun z ↦ (auxiliaryCoefficientGroupIso g).hom.hom.hom.hom.left ≫ z)
      (GroupSchemeBaseChange.congrIso_hom_fst (auxiliaryPointSections_base a) G))

/-- The comparison identifies the whole proper curves, including actions and zero. -/
irreducible_def cyclicHomAffineSourceCurveIso :
    auxiliaryPullbackCurve g ≅ cyclicHomSourceCurve n f := by
  let e : (auxiliaryPullbackCurve g).group ≅ (cyclicHomSourceCurve n f).group :=
    (CommGrp.forget _).mapIso (cyclicHomAffineSourceGroupIso n f)
  let _ : IsMonHom e.hom :=
    inferInstanceAs (IsMonHom (cyclicHomAffineSourceGroupIso n f).hom.hom.hom.hom)
  let _ := SmoothOfRelativeDimension.smooth 1 (cyclicHomSourceCurve n f).curve.hom
  exact isoOfSmoothGroup _ _ e

/-- The full comparison uses the actual original group isomorphism. -/
theorem cyclicHomAffineSourceCurveIso_group :
    (cyclicHomAffineSourceCurveIso n f).hom.group =
      (cyclicHomAffineSourceGroupIso n f).hom.hom.hom.hom := by
  rw [cyclicHomAffineSourceCurveIso_def]
  rfl

end FLT.Mazur.OddWeierstrassParameter
