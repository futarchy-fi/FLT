/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GroupSchemeBaseChangeEqualityComparison
public import FLT.Mazur.GroupSchemeBaseChangeProjections
public import FLT.Mazur.UniversalWeierstrassAuxiliaryFixedCoefficientComparison
public import FLT.Mazur.UniversalWeierstrassAuxiliarySchemeGroupComparison
public import FLT.Mazur.UniversalWeierstrassAuxiliarySchemeNormalizationRetraction

/-!
# Normalization fixes the entire group family on every normalized source

The coefficient comparison square descends from global sections to arbitrary
schemes. The resulting equality controls the actual full group map, including
all cyclic sections and nonreduced sources.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
open WeierstrassIntegralChart GroupSchemeBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {T : Scheme} (f : T ⟶ levelFour.left)
  (hn : SatisfiesNormalization f.appTop.hom)
local notation "G" => integralCurveGroup smoothEquation smoothEquation_discriminant

include hn in
/-- The normalized actual coefficient map is the original coefficient map on the slice. -/
theorem auxiliarySchemeNormalizedBase_fixed :
    auxiliarySchemeNormalizedPoint f ≫ levelFour.hom = f ≫ levelFour.hom := by
  rw [auxiliarySchemeNormalizedPoint_fixed f hn]

/-- The actual source coefficient comparison commutes with the identity normalization. -/
theorem auxiliarySchemeCoefficientComparison_fixed :
    auxiliarySchemeNormalizedCoefficientGroupIso f ≪≫
        congrIso (auxiliarySchemeNormalizedBase_fixed f hn) G =
      (Over.pullback T.toSpecΓ).mapCommGrp.mapIso
          (auxiliaryNormalizationGroupIso f.appTop.hom) ≪≫
        auxiliarySchemeCoefficientGroupIso f := by
  rw [auxiliarySchemeNormalizedCoefficientGroupIso_def, auxiliarySchemeCoefficientGroupIso_def]
  exact equalityComparison_congr T.toSpecΓ G
    (auxiliarySchemeNormalizedPoint_base f).symm (auxiliarySchemeSections_base f)
    (auxiliaryNormalizedCoefficientGroupIso f.appTop.hom)
    (auxiliaryCoefficientGroupIso f.appTop.hom) (auxiliaryNormalizationGroupIso f.appTop.hom)
    (auxiliaryNormalizedCoefficientBase_fixed f.appTop.hom hn)
    (auxiliarySchemeNormalizedBase_fixed f hn)
    (auxiliaryNormalizationGroupIso_coefficient_fixed f.appTop.hom hn)

/-- The entire actual normalization is equality transport on every normalized scheme family. -/
theorem auxiliarySchemeNormalizationGroupIso_fixed :
    auxiliarySchemeNormalizationGroupIso f =
      congrIso (auxiliarySchemeNormalizedBase_fixed f hn) G := by
  rw [auxiliarySchemeNormalizationGroupIso_def]
  exact (congrArg (fun e ↦ (auxiliarySchemeNormalizedCoefficientGroupIso f).symm ≪≫ e)
    (auxiliarySchemeCoefficientComparison_fixed f hn).symm).trans
      (Iso.symm_self_id_assoc _ _)

include hn in
/-- Every original source section projects unchanged through inverse normalization on the slice. -/
@[reassoc] theorem auxiliarySchemeNormalizationGroupIso_fixed_inv_fst :
    (auxiliarySchemeNormalizationGroupIso f).inv.hom.hom.hom.left ≫
        pullback.fst universalGroup.hom (auxiliarySchemeNormalizedPoint f ≫ levelFour.hom) =
      pullback.fst universalGroup.hom (f ≫ levelFour.hom) := by
  rw [auxiliarySchemeNormalizationGroupIso_fixed f hn]
  exact congrIso_hom_fst (auxiliarySchemeNormalizedBase_fixed f hn).symm G

end FLT.Mazur.UniversalWeierstrass
