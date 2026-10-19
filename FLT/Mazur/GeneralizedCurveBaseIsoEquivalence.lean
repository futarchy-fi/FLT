/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedComparisonBetweenRestriction

/-!
# Full comparison equivalences under an isomorphism of test schemes

Pullback along a scheme isomorphism is an equivalence of generalized curves.
Conjugating by the original-family transports therefore gives a bijection on
full comparisons with explicitly specified endpoint base maps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme}

/-- Base change along a scheme isomorphism is an equivalence of full DR categories. -/
def baseIsoEquivalence (a : T ≅ S) :
    GeneralizedEllipticCurve S ≌ GeneralizedEllipticCurve T :=
  CategoryTheory.Equivalence.mk (baseChangeFunctor a.hom) (baseChangeFunctor a.inv)
    (baseChangeId.symm ≪≫ baseChangeCongr a.inv_hom_id.symm ≪≫
      baseChangeComp a.hom a.inv)
    ((baseChangeComp a.inv a.hom).symm ≪≫ baseChangeCongr a.hom_inv_id ≪≫ baseChangeId)

/-- The equivalence uses the actual base-change functor. -/
theorem baseIsoEquivalence_functor (a : T ≅ S) :
    (baseIsoEquivalence a).functor = baseChangeFunctor a.hom := rfl

variable {S' P Q : Scheme}
  (E : GeneralizedEllipticCurve S) (F : GeneralizedEllipticCurve S')
  (g : P ⟶ S) (j : P ⟶ S') (a : Q ≅ P)
  (q : Q ⟶ S) (r : Q ⟶ S') (hq : q = a.hom ≫ g) (hr : r = a.hom ≫ j)

/-- An isomorphism of tests induces a bijection on original-family comparisons. -/
def comparisonBaseIsoEquiv :
    (E.baseChange g ≅ F.baseChange j) ≃ (E.baseChange q ≅ F.baseChange r) :=
  ((baseIsoEquivalence a).fullyFaithfulFunctor.isoEquiv).trans
    { toFun := fun e ↦ E.baseChangeCompEqIso g a.hom q hq ≪≫ e ≪≫
        (F.baseChangeCompEqIso j a.hom r hr).symm
      invFun := fun e ↦ (E.baseChangeCompEqIso g a.hom q hq).symm ≪≫ e ≪≫
        F.baseChangeCompEqIso j a.hom r hr
      left_inv := fun e ↦ by ext; simp
      right_inv := fun e ↦ by ext; simp }

/-- The comparison equivalence is exactly original-family pullback. -/
theorem comparisonBaseIsoEquiv_apply (e : E.baseChange g ≅ F.baseChange j) :
    comparisonBaseIsoEquiv E F g j a q r hq hr e =
      comparisonPullbackBetween E F g j a.hom q r hq hr e := rfl

end FLT.Mazur.GeneralizedEllipticCurve
