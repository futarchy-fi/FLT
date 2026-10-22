/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveBaseChangeSquare
public import FLT.Mazur.GeneralizedCurveGroupSectionComposition

/-!
# Original markings on two independently restricted families

A commuting square compares the restrictions through two different base charts.
The comparison carries the actual group marking and the whole curve projection.
The base charts need not be affine, and neither path needs to be flat.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T U V : Scheme} (E : GeneralizedEllipticCurve S)
  (g : T ⟶ S) (h : U ⟶ S) (p : V ⟶ T) (q : V ⟶ U)
  (w : q ≫ h = p ≫ g)
local notation "e" => Iso.app (baseChangeSquare g h q p w) E

/-- The overlap comparison preserves the independently pulled original group point. -/
theorem smoothMarkingOverlap_group (s : 𝟙_ (Over S) ⟶ E.group) :
    pullSection q (pullSection h s) ≫ (e).hom.group =
      pullSection p (pullSection g s) := by
  rw [← E.baseChangeCompIso_groupSection h q s, baseChangeSquare_app]
  change (pullSection (q ≫ h) s ≫ (E.baseChangeCompIso h q).hom.group) ≫
    ((E.baseChangeCompIso h q).inv.group ≫
      (E.baseChangeCompEqIso g p (q ≫ h) w).hom.group) = _
  have hi := congrArg (fun f ↦ f.group) (E.baseChangeCompIso h q).hom_inv_id
  change (E.baseChangeCompIso h q).hom.group ≫
    (E.baseChangeCompIso h q).inv.group = 𝟙 _ at hi
  rw [Category.assoc, ← Category.assoc (E.baseChangeCompIso h q).hom.group,
    hi, Category.id_comp]
  exact E.baseChangeCompEqIso_groupSection g p (q ≫ h) w s

/-- The overlap isomorphism retains the projection to the entire original curve. -/
@[reassoc] theorem smoothMarkingOverlap_projection :
    (e).hom.curve.left ≫ Limits.pullback.fst (E.baseChange g).curve.hom p ≫
      Limits.pullback.fst E.curve.hom g =
    Limits.pullback.fst (E.baseChange h).curve.hom q ≫
      Limits.pullback.fst E.curve.hom h := by
  rw [baseChangeSquare_app]
  change ((E.baseChangeCompIso h q).inv.curve.left ≫
    (E.baseChangeCompEqIso g p (q ≫ h) w).hom.curve.left) ≫ _ = _
  rw [Category.assoc, baseChangeCompEqIso_curve_fst,
    ← E.baseChangeCompIso_fst_fst h q, ← Category.assoc]
  have hi := ((forgetCurve ⋙ Over.forget V).mapIso (E.baseChangeCompIso h q)).inv_hom_id
  change (E.baseChangeCompIso h q).inv.curve.left ≫
    (E.baseChangeCompIso h q).hom.curve.left = 𝟙 _ at hi
  rw [hi, Category.id_comp]

end FLT.Mazur.GeneralizedEllipticCurve
