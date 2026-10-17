/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassAuxiliaryAffineCubicProjection

/-!
# Actual affine-source family comparisons induce proper cubic comparisons

Conjugating by the original cubic projections preserves the base, origin, and
all auxiliary sections. Marked comparison hypotheses are derived from the
original family isomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {T : Scheme} [IsAffine T] (f g : T ⟶ levelThree.left)
  (e : (auxiliarySchemeGroup f).X ≅ (auxiliarySchemeGroup g).X)

/-- The proper cubic comparison induced by the actual original affine-source families. -/
def auxiliaryAffineCubicIso :
    integralCurve (auxiliaryPullbackEquation f.appTop.hom) ≅
      integralCurve (auxiliaryPullbackEquation g.appTop.hom) :=
  (asIso (auxiliarySchemeOriginalCubicProjection f)).symm ≪≫
    (Over.forget T).mapIso e ≪≫ asIso (auxiliarySchemeOriginalCubicProjection g)

/-- The induced comparison commutes with the original cubic projections. -/
@[reassoc] theorem auxiliaryAffineCubicIso_projection :
    auxiliarySchemeOriginalCubicProjection f ≫ (auxiliaryAffineCubicIso f g e).hom =
      e.hom.left ≫ auxiliarySchemeOriginalCubicProjection g := by
  simp only [auxiliaryAffineCubicIso, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    asIso_inv, Functor.mapIso_hom, Over.forget_map, IsIso.hom_inv_id_assoc]

/-- The induced proper comparison preserves the original base over global sections. -/
@[reassoc] theorem auxiliaryAffineCubicIso_base :
    (auxiliaryAffineCubicIso f g e).hom ≫
      integralCurveStructure (auxiliaryPullbackEquation g.appTop.hom) =
        integralCurveStructure (auxiliaryPullbackEquation f.appTop.hom) := by
  apply (cancel_epi (auxiliarySchemeOriginalCubicProjection f)).mp
  rw [← Category.assoc, auxiliaryAffineCubicIso_projection, Category.assoc,
    auxiliarySchemeOriginalCubicProjection_structure, ← Category.assoc, e.hom.w,
    auxiliarySchemeOriginalCubicProjection_structure]

variable (hm : ∀ c : Labels 3, auxiliarySchemeMarking f c ≫ e.hom = auxiliarySchemeMarking g c)

include hm in
/-- Actual auxiliary-label compatibility recovers compatibility of the evaluated sections. -/
theorem auxiliaryAffineCubicIso_section (c : Labels 3) (hc : c ≠ 1) :
    auxiliaryPullbackSection f.appTop.hom c hc ≫ (auxiliaryAffineCubicIso f g e).hom =
      auxiliaryPullbackSection g.appTop.hom c hc := by
  apply (cancel_epi T.toSpecΓ).mp
  rw [← Category.assoc, ← auxiliarySchemeMarking_cubic_section f c hc,
    Category.assoc, auxiliaryAffineCubicIso_projection, ← Category.assoc, ← Over.comp_left,
    hm c, auxiliarySchemeMarking_cubic_section]

include hm in
/-- The identity label forces preservation of the original proper zero section. -/
theorem auxiliaryAffineCubicIso_zero :
    integralCurveZero (auxiliaryPullbackEquation f.appTop.hom) ≫
      (auxiliaryAffineCubicIso f g e).hom =
        integralCurveZero (auxiliaryPullbackEquation g.appTop.hom) := by
  apply (cancel_epi T.toSpecΓ).mp
  rw [← Category.assoc, ← auxiliarySchemeMarking_cubic_one f,
    Category.assoc, auxiliaryAffineCubicIso_projection, ← Category.assoc, ← Over.comp_left,
    hm 1, auxiliarySchemeMarking_cubic_one]

end FLT.Mazur.OddWeierstrassParameter
