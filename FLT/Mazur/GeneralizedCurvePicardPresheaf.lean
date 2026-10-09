/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurvePicardClasses

/-!
# The presheaf of generalized curves with Picard classes

The canonical generalized-curve comparisons retain the original projections.
Their Picard pullbacks give the identity and composition laws on classes.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.GeneralizedEllipticCurve

/-- Identity base change preserves the curve and its actual line-bundle class. -/
theorem curvePicardClassesPullback_id (S : Scheme) :
    curvePicardClassesPullback (𝟙 S) = id := by
  funext x
  refine Quotient.inductionOn x fun a ↦ ?_
  refine Quotient.sound ⟨a.1.baseChangeIdIso, ?_⟩
  change a.2 = SchemePicard.pullback a.1.baseChangeIdIso.inv.curve.left
    (SchemePicard.pullback (pullback.fst a.1.curve.hom (𝟙 S)) a.2)
  have hi : a.1.baseChangeIdIso.inv.curve.left ≫
      pullback.fst a.1.curve.hom (𝟙 S) = 𝟙 _ := by
    rw [← baseChangeIdIso_left]
    exact ((forgetCurve ⋙ Over.forget S).mapIso a.1.baseChangeIdIso).inv_hom_id
  have hc := SchemePicard.pullback_comp a.1.baseChangeIdIso.inv.curve.left
    (pullback.fst a.1.curve.hom (𝟙 S)) a.2
  rw [hi, SchemePicard.pullback_id] at hc
  exact hc

/-- Iterated geometric and sheaf pullback agree with restriction along the composite. -/
theorem curvePicardClassesPullback_comp {S T U : Scheme} (g : T ⟶ S) (h : U ⟶ T) :
    curvePicardClassesPullback (h ≫ g) =
      curvePicardClassesPullback h ∘ curvePicardClassesPullback g := by
  funext x
  refine Quotient.inductionOn x fun a ↦ ?_
  refine Quotient.sound ⟨a.1.baseChangeCompIso g h, ?_⟩
  let e := a.1.baseChangeCompIso g h
  have hi := ((forgetCurve ⋙ Over.forget U).mapIso e).inv_hom_id
  change e.inv.curve.left ≫ e.hom.curve.left = 𝟙 _ at hi
  have hp : e.inv.curve.left ≫ pullback.fst a.1.curve.hom (h ≫ g) =
      pullback.fst (a.1.baseChange g).curve.hom h ≫ pullback.fst a.1.curve.hom g := by
    rw [← a.1.baseChangeCompIso_fst_fst g h]
    change e.inv.curve.left ≫ e.hom.curve.left ≫ _ ≫ _ = _
    rw [← Category.assoc, hi, Category.id_comp]
  change SchemePicard.pullback _ (SchemePicard.pullback _ a.2) =
    SchemePicard.pullback e.inv.curve.left (SchemePicard.pullback _ a.2)
  rw [← SchemePicard.pullback_comp, ← SchemePicard.pullback_comp, hp]
  rfl

/-- The presheaf retaining a generalized curve and a line-bundle class on it. -/
def curvePicardClassPresheaf : Schemeᵒᵖ ⥤ Type 1 where
  obj S := curvePicardClasses S.unop
  map f := ↾(curvePicardClassesPullback f.unop)
  map_id S := by
    ext x
    exact congrFun (curvePicardClassesPullback_id S.unop) x
  map_comp f g := by
    ext x
    exact congrFun (curvePicardClassesPullback_comp f.unop g.unop) x

end FLT.Mazur.GeneralizedEllipticCurve
