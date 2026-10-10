/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassParameter
public import FLT.Mazur.AuxiliaryLevelFaithfulRepresentation
public import FLT.Mazur.WeierstrassGeneralizedEllipticModel
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Group.TypeTags.Finite

/-!
# Auxiliary markings on the universal smooth Weierstrass family

Apply the equation and open constructions to the actual universal cubic.
The label group is (Z/n)^2. In particular n = 4 gives an auxiliary marking
scheme over Z[1/2], retaining characteristic three. No assertion that this
parameterized family is already the modular atlas or covers it is made here.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry MonObj

namespace FLT.Mazur.UniversalWeierstrass

open AuxiliaryLevel WeierstrassIntegralChart

/-- The actual affine parameter scheme for the universal smooth cubic. -/
def parameterBase : Scheme := Spec (.of ParameterRing)

/-- The universal cubic with its constructed genus-one family, group, and action. -/
def universalCurve : GeneralizedEllipticCurve parameterBase :=
  integralGeneralizedEllipticCurve smoothEquation smoothEquation_discriminant

/-- The group of the original smooth universal cubic. -/
abbrev universalGroup : Over parameterBase := universalCurve.group

/-- Properness of the constructed cubic supplies the required separated group. -/
instance universalGroup_separated : IsSeparated universalGroup.hom := by
  change IsSeparated (integralCurveStructure smoothEquation)
  infer_instance

/-- The two-dimensional constant auxiliary label group. -/
abbrev Labels (n : ℕ) := Multiplicative (ZMod n × ZMod n)

/-- The label group has the expected n-squared order. -/
theorem labels_card (n : ℕ) [NeZero n] : Fintype.card (Labels n) = n ^ 2 := by
  simp [Labels, pow_two]

/-- Every label is killed by n. -/
theorem labels_pow (n : ℕ) (a : Labels n) : a ^ n = 1 :=
  congrArg Multiplicative.ofAdd (ZModModule.char_nsmul_eq_zero n a.toAdd)

/-- The actual open scheme of universally faithful markings of the universal cubic. -/
def auxiliaryScheme (n : ℕ) [NeZero n] : Over parameterBase :=
  faithfulScheme universalGroup (Labels n)

/-- Its finite relabeling action is constructed on the actual scheme. -/
def auxiliaryAction (n : ℕ) [NeZero n] :
    MulAut (Labels n) →* Aut (auxiliaryScheme n).left :=
  faithfulAction universalGroup (Labels n)

/-- The actual open inclusion in the finite marking equation scheme. -/
def auxiliaryInclusion (n : ℕ) [NeZero n] :
    auxiliaryScheme n ⟶ homScheme universalGroup (Labels n) :=
  faithfulInclusion universalGroup (Labels n)

/-- The universal auxiliary marking as sections of the universal group. -/
def auxiliaryMarking (n : ℕ) [NeZero n] :
    Labels n →* (auxiliaryScheme n ⟶ universalGroup) :=
  markingOf universalGroup (Labels n) (auxiliaryInclusion n)

/-- The marked sections lie in the actual n-torsion of the group scheme. -/
theorem auxiliaryMarking_pow (n : ℕ) [NeZero n] (a : Labels n) :
    auxiliaryMarking n a ^ n = 1 := by
  rw [← map_pow, labels_pow, map_one]

/-- Every nonempty test scheme sees an injective auxiliary marking. -/
theorem auxiliaryMarking_injective (n : ℕ) [NeZero n] {U : Over parameterBase}
    (f : U ⟶ auxiliaryScheme n) [Nonempty U.left] :
    Function.Injective (markingOf universalGroup (Labels n) (f ≫ auxiliaryInclusion n)) :=
  faithful_marking_injective universalGroup (Labels n) f

/-- Relabeling preserves the original arithmetic parameter map. -/
@[reassoc] theorem auxiliaryAction_base (n : ℕ) [NeZero n] (e : MulAut (Labels n)) :
    (auxiliaryAction n e).hom ≫ (auxiliaryScheme n).hom = (auxiliaryScheme n).hom :=
  faithfulAction_base universalGroup (Labels n) e

/-- The concrete auxiliary level-four parameter scheme. -/
def levelFour : Over parameterBase := auxiliaryScheme 4

/-- A smooth characteristic-three equation with its full five-coefficient interpretation. -/
def characteristicThreeEquation : WeierstrassCurve (ZMod 3) := ⟨0, 0, 0, -1, 0⟩

/-- The parameter scheme really has a characteristic-three point. -/
def characteristicThreeMap : ParameterRing →+* ZMod 3 :=
  specialize characteristicThreeEquation
    ⟨⟨2, 2, by decide, by decide⟩, rfl⟩ (by
      have h : characteristicThreeEquation.Δ = 1 := by decide
      rw [h]
      exact isUnit_one)

/-- That point recovers its original equation under the universal specialization. -/
theorem characteristicThree_specialization :
    smoothEquation.map characteristicThreeMap = characteristicThreeEquation :=
  smoothEquation_specialize _ _ _

end FLT.Mazur.UniversalWeierstrass
