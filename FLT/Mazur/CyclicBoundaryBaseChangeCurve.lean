/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryBaseChangeProjection
public import FLT.Mazur.CyclicBoundaryUniversalSubgroup
public import FLT.Mazur.GeneralizedCurveBaseChangeCompEq

/-!
# The full universal boundary curve under arbitrary base change

The faithful parameter comparison identifies the actual universal curves,
including their smooth groups and whole-curve actions. Both original projection
formulas are retained without imposing smoothness on the full curve.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (g : T ⟶ S) (E : GeneralizedEllipticCurve S)
  [IsSeparated E.group.hom] (n : ℕ) [NeZero n]

local instance boundaryCurvePullbackGroup_separated :
    IsSeparated (E.baseChange g).group.hom :=
  inferInstanceAs (IsSeparated (pullback.snd E.group.hom g))

local notation "P" => cyclicFaithfulParameter E.group n
local notation "Q" =>
  cyclicFaithfulParameter (GeneralizedEllipticCurve.group (E.baseChange g)) n
local notation "q" => faithfulBaseChangeToOriginal g E.group n

/-- The full actual universal boundary curves compare over the constructed parameter map. -/
def faithfulBaseChangeCurveIso :
    faithfulUniversalCurve (E.baseChange g) n ≅ (faithfulUniversalCurve E n).baseChange (q) :=
  (E.baseChangeCompIso g (Q).hom).symm ≪≫
    E.baseChangeCompEqIso (P).hom (q) ((Q).hom ≫ g)
      (faithfulBaseChangeToOriginal_base g E.group n).symm

/-- The curve comparison retains the two actual projections to the original whole curve. -/
@[reassoc] theorem faithfulBaseChangeCurveIso_curve_fst :
    (faithfulBaseChangeCurveIso g E n).hom.curve.left ≫
      pullback.fst (faithfulUniversalCurve E n).curve.hom (q) ≫
        pullback.fst E.curve.hom (P).hom =
      pullback.fst (E.baseChange g).curve.hom (Q).hom ≫ pullback.fst E.curve.hom g := by
  change ((E.baseChangeCompIso g (Q).hom).inv.curve.left ≫
    (E.baseChangeCompEqIso (P).hom (q) ((Q).hom ≫ g) _).hom.curve.left) ≫ _ = _
  rw [Category.assoc]
  exact (congrArg ((E.baseChangeCompIso g (Q).hom).inv.curve.left ≫ ·)
    (E.baseChangeCompEqIso_curve_fst (P).hom (q) ((Q).hom ≫ g)
      (faithfulBaseChangeToOriginal_base g E.group n).symm)).trans
        (OverPullbackSection.comp_inv_fst (Q).hom g E.curve)

/-- The smooth-group comparison retains the same original group projections. -/
@[reassoc] theorem faithfulBaseChangeCurveIso_group_fst :
    (faithfulBaseChangeCurveIso g E n).hom.group.left ≫
      pullback.fst (faithfulUniversalCurve E n).group.hom (q) ≫
        pullback.fst E.group.hom (P).hom =
      pullback.fst (E.baseChange g).group.hom (Q).hom ≫ pullback.fst E.group.hom g := by
  change ((E.baseChangeCompIso g (Q).hom).inv.group.left ≫
    (E.baseChangeCompEqIso (P).hom (q) ((Q).hom ≫ g) _).hom.group.left) ≫ _ = _
  rw [Category.assoc]
  exact (congrArg ((E.baseChangeCompIso g (Q).hom).inv.group.left ≫ ·)
    (E.baseChangeCompEqIso_group_fst (P).hom (q) ((Q).hom ≫ g)
      (faithfulBaseChangeToOriginal_base g E.group n).symm)).trans
        (OverPullbackSection.comp_inv_fst (Q).hom g E.group)

end FLT.Mazur.CyclicBoundaryParameter
