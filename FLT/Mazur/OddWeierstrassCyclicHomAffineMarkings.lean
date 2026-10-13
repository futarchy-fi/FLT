/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomAffineSource

/-!
# Both markings on the actual affine cyclic source

The auxiliary marking and every cyclic label survive the comparison with the
original auxiliary coefficient cubic. Repeated cyclic labels are retained.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OddWeierstrassParameter
open AuxiliaryLevel
open UniversalWeierstrass (Labels)
open IntegralWeierstrassParameter (oddChartEquation oddChart_discriminant)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (n : ℕ) [NeZero n]
  (f : Spec (.of R) ⟶ (cyclicHomAuxiliaryScheme n).left)
local notation "a" => cyclicHomAuxiliaryPoint n f
local notation "g" => auxiliaryPointSections a

/-- The original cyclic labels realized on the auxiliary coefficient cubic. -/
def cyclicHomAffineMarking : Multiplicative (ZMod n) →*
    (𝟙_ (Over (Spec (.of R))) ⟶ (auxiliaryPullbackGroup g).X) :=
  GroupMarkingTransport.transport _ _ (cyclicHomAffineSourceGroupIso n f).symm
    (cyclicHomSourceMarking n f)

/-- Every cyclic label returns to the original source under the full curve comparison. -/
theorem cyclicHomAffineMarking_source (i : Multiplicative (ZMod n)) :
    cyclicHomAffineMarking n f i ≫ (cyclicHomAffineSourceCurveIso n f).hom.group =
      cyclicHomSourceMarking n f i := by
  rw [cyclicHomAffineSourceCurveIso_group]
  exact DFunLike.congr_fun
    (GroupMarkingTransport.transport_symm_transport _ _
      (cyclicHomAffineSourceGroupIso n f).symm (cyclicHomSourceMarking n f)) i

/-- Realize the original auxiliary labels on the cyclic source. -/
def cyclicHomSourceAuxiliaryMarking : Labels 3 →*
    (𝟙_ (Over (Spec (.of R))) ⟶ (cyclicHomSourceCurve n f).group) :=
  GroupMarkingBaseChange.marking (a ≫ levelThree.hom) universalGroup _
    (markingOf universalGroup (Labels 3)
      (Over.homMk a (by simp) ≫ levelThreeInclusion))

/-- Each source auxiliary label projects to the actual original parameter. -/
@[reassoc] theorem cyclicHomSourceAuxiliaryMarking_fst (i : Labels 3) :
    (cyclicHomSourceAuxiliaryMarking n f i).left ≫
      pullback.fst universalGroup.hom (a ≫ levelThree.hom) =
        a ≫ (levelThreeInclusion ≫ value universalGroup (Labels 3) i).left := by
  have h := GroupMarkingBaseChange.marking_fst (a ≫ levelThree.hom) universalGroup
    (𝟙_ (Over (Spec (.of R))))
    (markingOf universalGroup (Labels 3)
      (Over.homMk a (by simp) ≫ levelThreeInclusion)) i
  exact h.trans (by
    change (a ≫ levelThreeInclusion.left) ≫ (value universalGroup (Labels 3) i).left = _
    rw [Over.comp_left, Category.assoc])

/-- The coefficient-cubic auxiliary label has the same original projection. -/
theorem cyclicHomAffineAuxiliary_projection (i : Labels 3) :
    (markingOf (auxiliaryPullbackGroup g).X (Labels 3)
      (auxiliaryOriginalParameter g (auxiliaryRelativePoint a) ≫
        faithfulInclusion (auxiliaryPullbackGroup g).X (Labels 3)) i).left ≫
      (auxiliaryCoefficientGroupIso g).hom.hom.hom.hom.left ≫
        pullback.fst universalGroup.hom (auxiliaryCoefficientBase g) =
          a ≫ (levelThreeInclusion ≫ value universalGroup (Labels 3) i).left := by
  change (auxiliaryOriginalParameter g (auxiliaryRelativePoint a) ≫
    faithfulInclusion (auxiliaryPullbackGroup g).X (Labels 3) ≫
      value (auxiliaryPullbackGroup g).X (Labels 3) i).left ≫ _ = _
  rw [auxiliaryOriginalParameter_def, cartesianGroupParameter_value]
  exact cartesianGroupMarking_projection (auxiliaryCoefficientBase g)
    (WeierstrassIntegralChart.integralCurveGroup oddChartEquation oddChart_discriminant)
    (auxiliaryPullbackGroup g) (auxiliaryCoefficientGroupIso g).symm
    (Labels 3) (auxiliaryRelativePoint a) i

/-- The original auxiliary labels agree on the entire source curve. -/
theorem cyclicHomAffineSource_auxiliary (i : Labels 3) :
    markingOf (auxiliaryPullbackGroup g).X (Labels 3)
        (auxiliaryOriginalParameter g (auxiliaryRelativePoint a) ≫
          faithfulInclusion (auxiliaryPullbackGroup g).X (Labels 3)) i ≫
      (cyclicHomAffineSourceCurveIso n f).hom.group =
        cyclicHomSourceAuxiliaryMarking n f i := by
  rw [cyclicHomAffineSourceCurveIso_group]
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · rw [Over.comp_left, Category.assoc, cyclicHomAffineSourceGroupIso_fst,
      cyclicHomAffineAuxiliary_projection, cyclicHomSourceAuxiliaryMarking_fst]
  · exact Over.w _ |>.trans (Over.w _).symm

end FLT.Mazur.OddWeierstrassParameter
