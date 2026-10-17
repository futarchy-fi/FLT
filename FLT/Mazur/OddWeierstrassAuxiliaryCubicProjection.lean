/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassAuxiliaryProperNaturality
public import FLT.Mazur.OddWeierstrassAuxiliarySchemeMarkingComparison

/-!
# Actual cubic projections of arbitrary-source group families

The coefficient comparison gives each source family its original proper cubic
projection. This projection and the source structure map jointly detect maps.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {T : Scheme} (f : T ⟶ levelThree.left)

/-- The original source family projects to its actual cubic over global sections. -/
def auxiliarySchemeOriginalCubicProjection :
    (auxiliarySchemeGroup f).X.left ⟶ integralCurve (auxiliaryPullbackEquation f.appTop.hom) :=
  (auxiliarySchemeCoefficientGroupIso f).inv.hom.hom.hom.left ≫
    pullback.fst (auxiliaryPullbackGroup f.appTop.hom).X.hom T.toSpecΓ

/-- The normalized source family projects to its actual cubic over global sections. -/
def auxiliarySchemeNormalizedCubicProjection :
    (auxiliarySchemeGroup (auxiliarySchemeNormalizedPoint f)).X.left ⟶
      integralCurve (auxiliaryNormalizedEquation f.appTop.hom) :=
  (auxiliarySchemeNormalizedCoefficientGroupIso f).inv.hom.hom.hom.left ≫
    pullback.fst (auxiliaryNormalizedGroup f.appTop.hom).X.hom T.toSpecΓ

/-- The original cubic projection retains the source's canonical global-sections map. -/
@[reassoc] theorem auxiliarySchemeOriginalCubicProjection_structure :
    auxiliarySchemeOriginalCubicProjection f ≫
        integralCurveStructure (auxiliaryPullbackEquation f.appTop.hom) =
      (auxiliarySchemeGroup f).X.hom ≫ T.toSpecΓ := by
  change (_ ≫ pullback.fst _ _) ≫ (auxiliaryPullbackGroup f.appTop.hom).X.hom = _
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (fun z ↦ z ≫ T.toSpecΓ)
    (auxiliarySchemeCoefficientGroupIso f).inv.hom.hom.hom.w

/-- The normalized cubic projection retains the same canonical global-sections map. -/
@[reassoc] theorem auxiliarySchemeNormalizedCubicProjection_structure :
    auxiliarySchemeNormalizedCubicProjection f ≫
        integralCurveStructure (auxiliaryNormalizedEquation f.appTop.hom) =
      (auxiliarySchemeGroup (auxiliarySchemeNormalizedPoint f)).X.hom ≫ T.toSpecΓ := by
  change (_ ≫ pullback.fst _ _) ≫ (auxiliaryNormalizedGroup f.appTop.hom).X.hom = _
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (fun z ↦ z ≫ T.toSpecΓ)
    (auxiliarySchemeNormalizedCoefficientGroupIso f).inv.hom.hom.hom.w

/-- The original cubic and the unchanged source jointly detect all family morphisms. -/
theorem auxiliarySchemeOriginalCubicProjection_hom_ext {X : Scheme}
    (a b : X ⟶ (auxiliarySchemeGroup f).X.left)
    (hc : a ≫ auxiliarySchemeOriginalCubicProjection f =
      b ≫ auxiliarySchemeOriginalCubicProjection f)
    (hs : a ≫ (auxiliarySchemeGroup f).X.hom = b ≫ (auxiliarySchemeGroup f).X.hom) : a = b := by
  apply (cancel_mono (auxiliarySchemeCoefficientGroupIso f).inv.hom.hom.hom.left).mp
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans (hc.trans (Category.assoc _ _ _).symm)
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun z ↦ a ≫ z) (auxiliarySchemeCoefficientGroupIso f).inv.hom.hom.hom.w).trans
        (hs.trans ((congrArg (fun z ↦ b ≫ z)
          (auxiliarySchemeCoefficientGroupIso f).inv.hom.hom.hom.w).symm.trans
            (Category.assoc _ _ _).symm)))

/-- The normalized cubic and the unchanged source jointly detect all family morphisms. -/
theorem auxiliarySchemeNormalizedCubicProjection_hom_ext {X : Scheme}
    (a b : X ⟶ (auxiliarySchemeGroup (auxiliarySchemeNormalizedPoint f)).X.left)
    (hc : a ≫ auxiliarySchemeNormalizedCubicProjection f =
      b ≫ auxiliarySchemeNormalizedCubicProjection f)
    (hs : a ≫ (auxiliarySchemeGroup (auxiliarySchemeNormalizedPoint f)).X.hom =
      b ≫ (auxiliarySchemeGroup (auxiliarySchemeNormalizedPoint f)).X.hom) : a = b := by
  apply (cancel_mono (auxiliarySchemeNormalizedCoefficientGroupIso f).inv.hom.hom.hom.left).mp
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans (hc.trans (Category.assoc _ _ _).symm)
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun z ↦ a ≫ z)
        (auxiliarySchemeNormalizedCoefficientGroupIso f).inv.hom.hom.hom.w).trans
        (hs.trans ((congrArg (fun z ↦ b ≫ z)
          (auxiliarySchemeNormalizedCoefficientGroupIso f).inv.hom.hom.hom.w).symm.trans
            (Category.assoc _ _ _).symm)))

end FLT.Mazur.OddWeierstrassParameter
