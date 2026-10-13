/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntegralWeierstrassCharacteristicCover
public import FLT.Mazur.UniversalWeierstrassAuxiliaryLevel

/-!
# Level-three parameters on the odd coefficient chart

The actual discriminant-localized D(3) equation supplies a proper group scheme
and its faithful level-three parameter scheme, retaining characteristic two.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonObj
namespace FLT.Mazur.OddWeierstrassParameter
open AuxiliaryLevel WeierstrassIntegralChart
open IntegralWeierstrassParameter (OddChartRing oddChartEquation oddChart_discriminant)
open UniversalWeierstrass (Labels labels_pow)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The odd coefficient chart retains characteristic two. -/
def parameterBase : Scheme := Spec (.of OddChartRing)

/-- The actual universal proper cubic with its constructed group and regular action. -/
def universalCurve : GeneralizedEllipticCurve parameterBase :=
  integralGeneralizedEllipticCurve oddChartEquation oddChart_discriminant

/-- The entire smooth universal cubic, regarded as its group scheme. -/
abbrev universalGroup : Over parameterBase := universalCurve.group

/-- The constructed original group has separated structure map. -/
instance universalGroup_separated : IsSeparated universalGroup.hom := by
  change IsSeparated (integralCurveStructure oddChartEquation)
  infer_instance

/-- Faithful markings of the full original universal group are represented by an actual scheme. -/
def levelThree : Over parameterBase :=
  faithfulScheme universalGroup (Labels 3)

/-- The marking scheme retains the actual inclusion into all homomorphism parameters. -/
def levelThreeInclusion :
    levelThree ⟶ homScheme universalGroup (Labels 3) :=
  faithfulInclusion universalGroup (Labels 3)

/-- Every label is an actual section of the original universal group. -/
def levelThreeMarking :
    Labels 3 →* (levelThree ⟶ universalGroup) :=
  markingOf universalGroup (Labels 3) levelThreeInclusion

/-- The marked sections satisfy the original torsion equations. -/
theorem levelThreeMarking_pow (a : Labels 3) :
    levelThreeMarking a ^ 3 = 1 := by
  rw [← map_pow, labels_pow, map_one]

/-- Faithful markings are injective on every nonempty test scheme. -/
theorem levelThreeMarking_injective {U : Over parameterBase}
    (f : U ⟶ levelThree) [Nonempty U.left] :
    Function.Injective (markingOf universalGroup (Labels 3) (f ≫ levelThreeInclusion)) :=
  faithful_marking_injective universalGroup (Labels 3) f

/-- Auxiliary relabeling acts on the actual odd-chart scheme. -/
def levelThreeAction :
    MulAut (Labels 3) →* Aut levelThree.left :=
  faithfulAction universalGroup (Labels 3)

/-- Relabeling retains the original integral coefficient parameter. -/
@[reassoc] theorem levelThreeAction_base (e : MulAut (Labels 3)) :
    (levelThreeAction e).hom ≫ levelThree.hom = levelThree.hom :=
  faithfulAction_base universalGroup (Labels 3) e

/-- The characteristic-two coefficient point is a point of the actual smooth parameter scheme. -/
def characteristicTwoPoint : Spec (.of (ZMod 2)) ⟶ parameterBase :=
  Spec.map (CommRingCat.ofHom IntegralWeierstrassParameter.oddChartCharacteristicTwo)

end FLT.Mazur.OddWeierstrassParameter
