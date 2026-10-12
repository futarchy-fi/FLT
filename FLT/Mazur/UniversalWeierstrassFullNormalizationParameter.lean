/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AuxiliaryCartesianParameterEquivalence
public import FLT.Mazur.UniversalWeierstrassAuxiliarySchemeNormalizationMarking
public import FLT.Mazur.UniversalWeierstrassCyclicAuxiliary

/-!
# Complete faithful parameters through actual normalization

The normalization group comparison transports any finite faithful labeling,
including the entire auxiliary and cyclic product, over arbitrary source schemes.
The original coefficient map, normalization map, and full parameter are retained.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonObj
namespace FLT.Mazur.UniversalWeierstrass
open AuxiliaryLevel WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {T : Scheme} (a : T ⟶ levelFour.left) (A : Type) [Group A] [Fintype A]
local notation "G" => integralCurveGroup smoothEquation smoothEquation_discriminant
local notation "bO" => a ≫ levelFour.hom
local notation "bN" => auxiliarySchemeNormalizedPoint a ≫ levelFour.hom
local notation "e" => auxiliarySchemeNormalizationGroupIso a

/-- The actual universal group family remains separated after arbitrary base change. -/
instance auxiliarySchemeGroup_separated : IsSeparated (auxiliarySchemeGroup a).X.hom := by
  change IsSeparated (pullback.snd universalGroup.hom bO)
  infer_instance

/-- The full original parameter, realized on its actual group family. -/
def auxiliarySchemeFullOriginalParameter {U : Over T}
    (f : (Over.map bO).obj U ⟶ faithfulScheme universalGroup A) :
    U ⟶ faithfulScheme (auxiliarySchemeGroup a).X A :=
  cartesianGroupParameter bO G (auxiliarySchemeGroup a) (Iso.refl _) A f

/-- The actual normalized parameter retains any complete finite faithful labeling. -/
def auxiliarySchemeFullNormalizedParameter {U : Over T}
    (f : (Over.map bO).obj U ⟶ faithfulScheme universalGroup A) :
    (Over.map bN).obj U ⟶ faithfulScheme universalGroup A :=
  originalGroupParameter bN G (auxiliarySchemeGroup a) e A
    (auxiliarySchemeFullOriginalParameter a A f)

/-- Realizing the normalized parameter recovers the entire original realized parameter. -/
theorem auxiliarySchemeFullNormalizedParameter_compare {U : Over T}
    (f : (Over.map bO).obj U ⟶ faithfulScheme universalGroup A) :
    cartesianGroupParameter bN G (auxiliarySchemeGroup a) e A
      (auxiliarySchemeFullNormalizedParameter a A f) =
        auxiliarySchemeFullOriginalParameter a A f :=
  cartesianGroupParameter_original bN G (auxiliarySchemeGroup a) e A _

/-- Every normalized label is projected through the inverse actual normalization comparison. -/
theorem auxiliarySchemeFullNormalizedParameter_value {U : Over T}
    (f : (Over.map bO).obj U ⟶ faithfulScheme universalGroup A) (c : A) :
    (auxiliarySchemeFullNormalizedParameter a A f ≫ faithfulInclusion universalGroup A ≫
      value universalGroup A c).left =
        (auxiliarySchemeFullOriginalParameter a A f ≫
          faithfulInclusion (auxiliarySchemeGroup a).X A ≫
            value (auxiliarySchemeGroup a).X A c).left ≫
              (e).inv.hom.hom.hom.left ≫ pullback.fst universalGroup.hom bN :=
  (congrArg Over.Hom.left (originalGroupParameter_value bN G
    (auxiliarySchemeGroup a) e A _ c)).trans
      (originalGroupMarking_left bN G (auxiliarySchemeGroup a) e A _ c)

/-- The full original realization commutes with every test-scheme map. -/
@[reassoc] theorem auxiliarySchemeFullOriginalParameter_natural {U V : Over T}
    (f : (Over.map bO).obj U ⟶ faithfulScheme universalGroup A) (k : V ⟶ U) :
    k ≫ auxiliarySchemeFullOriginalParameter a A f =
      auxiliarySchemeFullOriginalParameter a A ((Over.map bO).map k ≫ f) :=
  cartesianGroupParameter_natural bO G (auxiliarySchemeGroup a) (Iso.refl _) A f k

/-- Full normalization is natural on all tests over the unchanged arbitrary source. -/
@[reassoc] theorem auxiliarySchemeFullNormalizedParameter_natural {U V : Over T}
    (f : (Over.map bO).obj U ⟶ faithfulScheme universalGroup A) (k : V ⟶ U) :
    (Over.map bN).map k ≫ auxiliarySchemeFullNormalizedParameter a A f =
      auxiliarySchemeFullNormalizedParameter a A ((Over.map bO).map k ≫ f) := by
  unfold auxiliarySchemeFullNormalizedParameter
  rw [originalGroupParameter_natural, auxiliarySchemeFullOriginalParameter_natural]

end FLT.Mazur.UniversalWeierstrass
