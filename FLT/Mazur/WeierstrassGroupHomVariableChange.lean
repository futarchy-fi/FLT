/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassVariableChangeGroup
public import FLT.Mazur.FiniteLocallyFreeDegreeAffine

/-!
# Actual group morphisms between changed Weierstrass equations

Conjugating by the original proper coordinate changes gives a map on the
specified equations. Its square is Cartesian and retains the original degree.
This applies to generic fibers of independently minimalized local models.
-/

@[expose] public noncomputable section

open WeierstrassCurve CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (E V W U : WeierstrassCurve R)
  (C D : VariableChange R) (hC : C • E = W) (hD : D • V = U)
  (hE : IsUnit E.Δ) (hV : IsUnit V.Δ) (hW : IsUnit W.Δ) (hU : IsUnit U.Δ)
  (f : integralCurveGroup E hE ⟶ integralCurveGroup V hV)

/-- The original group map on the specified changed source and target equations. -/
def integralGroupHomVariableChange : integralCurveGroup W hW ⟶ integralCurveGroup U hU :=
  (integralVariableChangeGroupIso E W C hC hE hW).hom ≫ f ≫
    (integralVariableChangeGroupIso V U D hD hV hU).inv

/-- The exact original coordinate changes identify the constructed scheme map. -/
@[reassoc] theorem integralGroupHomVariableChange_square :
    (integralGroupHomVariableChange E V W U C D hC hD hE hV hW hU f).hom.hom.hom.left ≫
        (integralVariableChangeIso V U D hD).hom =
      (integralVariableChangeIso E W C hC).hom ≫ f.hom.hom.hom.left := by
  have H : integralGroupHomVariableChange E V W U C D hC hD hE hV hW hU f ≫
      (integralVariableChangeGroupIso V U D hD hV hU).hom =
        (integralVariableChangeGroupIso E W C hC hE hW).hom ≫ f := by
    unfold integralGroupHomVariableChange
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have H' := congrArg (fun t : integralCurveGroup W hW ⟶ integralCurveGroup V hV ↦
    t.hom.hom.hom.left) H
  simpa only [CommGrp.comp_hom, Grp.comp_hom_hom, Over.comp_left,
    integralVariableChangeGroupIso_hom] using H'

/-- The original map is recovered in a Cartesian square of actual coordinate changes. -/
theorem integralGroupHomVariableChange_isPullback :
    IsPullback (integralVariableChangeIso E W C hC).hom
      (integralGroupHomVariableChange E V W U C D hC hD hE hV hW hU f).hom.hom.hom.left
      f.hom.hom.hom.left (integralVariableChangeIso V U D hD).hom :=
  IsPullback.of_horiz_isIso
    ⟨(integralGroupHomVariableChange_square E V W U C D hC hD hE hV hW hU f).symm⟩

/-- Changing the original source and target equations preserves the exact degree. -/
theorem integralGroupHomVariableChange_degree (d : ℕ)
    (hd : FCurve.FiniteLocallyFreeDegree f.hom.hom.hom.left d) :
    FCurve.FiniteLocallyFreeDegree
      (integralGroupHomVariableChange E V W U C D hC hD hE hV hW hU f).hom.hom.hom.left d :=
  FCurve.finiteLocallyFreeDegree_of_isPullback
    (integralGroupHomVariableChange_isPullback E V W U C D hC hD hE hV hW hU f) d hd

end FLT.Mazur.WeierstrassIntegralChart
