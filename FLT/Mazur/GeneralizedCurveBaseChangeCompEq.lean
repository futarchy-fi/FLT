/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveBaseChangeCoherence

/-!
# Full curve comparisons for equal composite base maps

Projection formulas for the curve and its group keep subsequent parameter
comparisons independent of the implementation of iterated base change.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T U : Scheme} (E : GeneralizedEllipticCurve S)

/-- Equality of base maps preserves the group projection. -/
@[reassoc] theorem baseChangeCongr_group_fst {f g : T ⟶ S} (h : f = g) :
    ((baseChangeCongr h).hom.app E).group.left ≫ pullback.fst E.group.hom g =
      pullback.fst E.group.hom f := by
  subst g
  exact Category.id_comp _

/-- The iterated comparison preserves the group projection. -/
@[reassoc] theorem baseChangeCompIso_group_fst_fst (g : T ⟶ S) (k : U ⟶ T) :
    (E.baseChangeCompIso g k).hom.group.left ≫
      pullback.fst (E.baseChange g).group.hom k ≫ pullback.fst E.group.hom g =
        pullback.fst E.group.hom (k ≫ g) :=
  OverPullbackCoherence.comp_left_fst_fst g k E.group

/-- Compare direct base change with an equal iterated base change as full curves. -/
def baseChangeCompEqIso (g : T ⟶ S) (k : U ⟶ T) (h : U ⟶ S) (w : h = k ≫ g) :
    E.baseChange h ≅ (E.baseChange g).baseChange k :=
  (baseChangeCongr w).app E ≪≫ E.baseChangeCompIso g k

variable (g : T ⟶ S) (k : U ⟶ T) (h : U ⟶ S) (w : h = k ≫ g)

/-- The equal-composite comparison retains the full original curve projection. -/
@[reassoc] theorem baseChangeCompEqIso_curve_fst :
    (E.baseChangeCompEqIso g k h w).hom.curve.left ≫
      pullback.fst (E.baseChange g).curve.hom k ≫ pullback.fst E.curve.hom g =
        pullback.fst E.curve.hom h := by
  change (((baseChangeCongr w).hom.app E).curve.left ≫
    (E.baseChangeCompIso g k).hom.curve.left) ≫ _ = _
  rw [Category.assoc, baseChangeCompIso_fst_fst, baseChangeCongr_fst]

/-- The equal-composite comparison retains the original group projection. -/
@[reassoc] theorem baseChangeCompEqIso_group_fst :
    (E.baseChangeCompEqIso g k h w).hom.group.left ≫
      pullback.fst (E.baseChange g).group.hom k ≫ pullback.fst E.group.hom g =
        pullback.fst E.group.hom h := by
  change (((baseChangeCongr w).hom.app E).group.left ≫
    (E.baseChangeCompIso g k).hom.group.left) ≫ _ = _
  rw [Category.assoc, baseChangeCompIso_group_fst_fst, baseChangeCongr_group_fst]

end FLT.Mazur.GeneralizedEllipticCurve
