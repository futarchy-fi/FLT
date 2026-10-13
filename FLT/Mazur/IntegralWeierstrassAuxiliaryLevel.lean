/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntegralWeierstrassParameter
public import FLT.Mazur.UniversalWeierstrassAuxiliaryLevel

/-!
# Actual auxiliary schemes for the all-characteristic smooth cubic

The discriminant-only universal family has its constructed proper curve and
group law. Its faithful level-three scheme is a candidate chart at two;
nonemptiness and covering properties are not assumed or asserted.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonObj
namespace FLT.Mazur.IntegralWeierstrassParameter
open AuxiliaryLevel WeierstrassIntegralChart
open UniversalWeierstrass (Labels labels_pow)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The smooth coefficient scheme includes every residue characteristic. -/
def parameterBase : Scheme := Spec (.of SmoothRing)

/-- The actual universal proper cubic with its constructed group and regular action. -/
def universalCurve : GeneralizedEllipticCurve parameterBase :=
  integralGeneralizedEllipticCurve smoothEquation smoothEquation_discriminant

/-- The entire smooth universal cubic, regarded as its group scheme. -/
abbrev universalGroup : Over parameterBase := universalCurve.group

/-- The constructed original group has separated structure map. -/
instance universalGroup_separated : IsSeparated universalGroup.hom := by
  change IsSeparated (integralCurveStructure smoothEquation)
  infer_instance

/-- Faithful markings of the full original universal group are represented by an actual scheme. -/
def auxiliaryScheme (n : ℕ) [NeZero n] : Over parameterBase :=
  faithfulScheme universalGroup (Labels n)

/-- The marking scheme retains the actual inclusion into all homomorphism parameters. -/
def auxiliaryInclusion (n : ℕ) [NeZero n] :
    auxiliaryScheme n ⟶ homScheme universalGroup (Labels n) :=
  faithfulInclusion universalGroup (Labels n)

/-- Every label is an actual section of the original universal group. -/
def auxiliaryMarking (n : ℕ) [NeZero n] :
    Labels n →* (auxiliaryScheme n ⟶ universalGroup) :=
  markingOf universalGroup (Labels n) (auxiliaryInclusion n)

/-- The marked sections satisfy the original torsion equations. -/
theorem auxiliaryMarking_pow (n : ℕ) [NeZero n] (a : Labels n) :
    auxiliaryMarking n a ^ n = 1 := by
  rw [← map_pow, labels_pow, map_one]

/-- Faithful markings are injective on every nonempty test scheme. -/
theorem auxiliaryMarking_injective (n : ℕ) [NeZero n] {U : Over parameterBase}
    (f : U ⟶ auxiliaryScheme n) [Nonempty U.left] :
    Function.Injective (markingOf universalGroup (Labels n) (f ≫ auxiliaryInclusion n)) :=
  faithful_marking_injective universalGroup (Labels n) f

/-- Auxiliary relabeling acts on the actual all-characteristic scheme. -/
def auxiliaryAction (n : ℕ) [NeZero n] :
    MulAut (Labels n) →* Aut (auxiliaryScheme n).left :=
  faithfulAction universalGroup (Labels n)

/-- Relabeling retains the original integral coefficient parameter. -/
@[reassoc] theorem auxiliaryAction_base (n : ℕ) [NeZero n] (e : MulAut (Labels n)) :
    (auxiliaryAction n e).hom ≫ (auxiliaryScheme n).hom = (auxiliaryScheme n).hom :=
  faithfulAction_base universalGroup (Labels n) e

/-- The actual auxiliary level-three parameter scheme available in characteristic two. -/
def levelThree : Over parameterBase := auxiliaryScheme 3

/-- The characteristic-two coefficient point is a point of the actual smooth parameter scheme. -/
def characteristicTwoPoint : Spec (.of (ZMod 2)) ⟶ parameterBase :=
  Spec.map (CommRingCat.ofHom characteristicTwoMap)

end FLT.Mazur.IntegralWeierstrassParameter
