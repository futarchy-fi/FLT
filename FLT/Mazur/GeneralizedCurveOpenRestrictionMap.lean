/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveGroupSectionComposition

/-!
# Direct restriction maps of the original whole curve

The actual family associator defines maps for inclusions of base opens.
Their identity and composition laws are detected by the open immersion into
the original whole curve, without affineness or separatedness of the base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : GeneralizedEllipticCurve S) (U V W : S.Opens)

/-- Restrict the entire original curve along an inclusion of base opens. -/
def openRestrictionCurveMap (h : W ≤ U) :
    (E.baseChange W.ι).curve.left ⟶ (E.baseChange U.ι).curve.left :=
  (E.baseChangeCompEqIso U.ι (S.homOfLE h) W.ι (Scheme.homOfLE_ι S h).symm).hom.curve.left ≫
    Limits.pullback.fst (E.baseChange U.ι).curve.hom (S.homOfLE h)

/-- Direct restriction preserves the map to the original whole curve. -/
@[reassoc] theorem openRestrictionCurveMap_fst (h : W ≤ U) :
    openRestrictionCurveMap E U W h ≫ Limits.pullback.fst E.curve.hom U.ι =
      Limits.pullback.fst E.curve.hom W.ι := by
  rw [openRestrictionCurveMap, Category.assoc, baseChangeCompEqIso_curve_fst]

/-- These direct whole-family maps are open immersions. -/
instance openRestrictionCurveMap_isOpenImmersion (h : W ≤ U) :
    IsOpenImmersion (openRestrictionCurveMap E U W h) := by
  unfold openRestrictionCurveMap
  let e := E.baseChangeCompEqIso U.ι (S.homOfLE h) W.ι (Scheme.homOfLE_ι S h).symm
  let _ : IsIso e.hom.curve.left := inferInstanceAs
    (IsIso (((forgetCurve ⋙ Over.forget W.toScheme).mapIso e).hom))
  infer_instance

/-- Restriction to the same open is the identity on the actual original curve. -/
theorem openRestrictionCurveMap_refl : openRestrictionCurveMap E U U le_rfl = 𝟙 _ := by
  apply (cancel_mono (Limits.pullback.fst E.curve.hom U.ι)).mp
  rw [openRestrictionCurveMap_fst, Category.id_comp]

/-- Successive restrictions agree with the direct original whole-family map. -/
theorem openRestrictionCurveMap_comp (h : W ≤ V) (k : V ≤ U) :
    openRestrictionCurveMap E V W h ≫ openRestrictionCurveMap E U V k =
      openRestrictionCurveMap E U W (h.trans k) := by
  apply (cancel_mono (Limits.pullback.fst E.curve.hom U.ι)).mp
  rw [Category.assoc, openRestrictionCurveMap_fst,
    openRestrictionCurveMap_fst, openRestrictionCurveMap_fst]

end FLT.Mazur.GeneralizedEllipticCurve
