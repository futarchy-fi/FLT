/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomSourceDivisor
public import FLT.Mazur.OddWeierstrassAuxiliarySchemeNormalizationMarking
public import FLT.Mazur.GroupMarkingCartesianInverse

/-!
# Normalization of unrestricted cyclic parameters

Normalize the auxiliary point and transport the cyclic marking separately
through the actual normalization group isomorphism. Their images may intersect;
no product marking or coprimality hypothesis is introduced.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
open IntegralWeierstrassParameter (oddChartEquation oddChart_discriminant)
open AuxiliaryLevel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme}
  (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)
local notation "a" => cyclicHomAuxiliaryPoint n f
local notation "G" =>
  WeierstrassIntegralChart.integralCurveGroup oddChartEquation oddChart_discriminant
local notation "bN" => auxiliarySchemeNormalizedPoint a ≫ levelThree.hom

/-- The auxiliary normalization as a relative point over its actual normalized coefficients. -/
def cyclicHomNormalizedAuxiliary :
    (Over.map bN).obj (𝟙_ (Over T)) ⟶ levelThree :=
  Over.homMk (auxiliarySchemeNormalizedPoint a) (Category.id_comp _).symm

/-- Transport all cyclic labels, allowing collisions, to the normalized universal group. -/
def cyclicHomNormalizedCyclic :
    (Over.map bN).obj (𝟙_ (Over T)) ⟶ homScheme universalGroup (Multiplicative (ZMod n)) :=
  liftMarking _ _ (GroupMarkingCartesianTransport.inverseMarking bN G
    (auxiliarySchemeGroup a) (auxiliarySchemeNormalizationGroupIso a) (𝟙_ (Over T))
    (cyclicHomSourceMarking n f))

/-- Each normalized cyclic value retains the full original section. -/
theorem cyclicHomNormalizedCyclic_value (c : Multiplicative (ZMod n)) :
    (cyclicHomNormalizedCyclic n f ≫ value universalGroup (Multiplicative (ZMod n)) c).left =
      (cyclicHomSourceMarking n f c).left ≫
        (auxiliarySchemeNormalizationGroupIso a).inv.hom.hom.hom.left ≫
          pullback.fst universalGroup.hom bN := by
  rw [cyclicHomNormalizedCyclic, liftMarking_value]
  exact GroupMarkingCartesianTransport.inverseMarking_left bN G
    (auxiliarySchemeGroup a) (auxiliarySchemeNormalizationGroupIso a) _ _ c

/-- The entire unrestricted parameter over the normalized coefficient map. -/
def cyclicHomNormalizedParameter :
    (Over.map bN).obj (𝟙_ (Over T)) ⟶ cyclicHomAuxiliaryScheme n :=
  cyclicHomLift n (cyclicHomNormalizedAuxiliary n f)
    (cyclicHomNormalizedCyclic n f)

/-- The actual normalized unrestricted point on the original test scheme. -/
def cyclicHomNormalizedPoint : T ⟶ (cyclicHomAuxiliaryScheme n).left :=
  (cyclicHomNormalizedParameter n f).left

/-- Normalization retains the previously constructed auxiliary normalization exactly. -/
@[reassoc] theorem cyclicHomNormalizedPoint_auxiliary :
    cyclicHomNormalizedPoint n f ≫ (cyclicHomAuxiliary n).left =
      auxiliarySchemeNormalizedPoint a :=
  congrArg Over.Hom.left (cyclicHomLift_auxiliary n _ _)

/-- The cyclic factor is transported through the established normalization comparison. -/
@[reassoc] theorem cyclicHomNormalizedPoint_cyclic :
    cyclicHomNormalizedPoint n f ≫ (cyclicHomParameter n).left =
      (cyclicHomNormalizedCyclic n f).left :=
  congrArg Over.Hom.left (cyclicHomLift_cyclic n _ _)

/-- The normalized point uses exactly the normalized auxiliary coefficient map. -/
@[reassoc] theorem cyclicHomNormalizedPoint_base :
    cyclicHomNormalizedPoint n f ≫ (cyclicHomAuxiliaryScheme n).hom = bN :=
  (cyclicHomNormalizedParameter n f).w.trans (Category.id_comp _)

/-- Every cyclic label retains its original section through the normalization group isomorphism. -/
theorem cyclicHomNormalizedPoint_value (c : Multiplicative (ZMod n)) :
    cyclicHomNormalizedPoint n f ≫ (cyclicHomParameter n ≫
      value universalGroup (Multiplicative (ZMod n)) c).left =
      (cyclicHomSourceMarking n f c).left ≫
        (auxiliarySchemeNormalizationGroupIso a).inv.hom.hom.hom.left ≫
          pullback.fst universalGroup.hom bN := by
  rw [Over.comp_left, ← Category.assoc, cyclicHomNormalizedPoint_cyclic]
  exact cyclicHomNormalizedCyclic_value n f c

end FLT.Mazur.OddWeierstrassParameter
