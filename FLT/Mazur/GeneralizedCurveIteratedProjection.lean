/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveBaseChangeCompEq

/-!
# Original curve projections detect iterated base-change morphisms

The structure map fixes all the base coordinates. Thus the projection to the
original curve detects a full morphism into a twice or three times pulled-back family.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T U V : Scheme} (E : GeneralizedEllipticCurve S)

/-- The inverse equal-composite comparison retains the original curve coordinate. -/
@[reassoc] theorem baseChangeCompEqIso_inv_curve_fst
    (g : T ⟶ S) (k : U ⟶ T) (h : U ⟶ S) (w : h = k ≫ g) :
    (E.baseChangeCompEqIso g k h w).inv.curve.left ≫ pullback.fst E.curve.hom h =
      pullback.fst (E.baseChange g).curve.hom k ≫ pullback.fst E.curve.hom g := by
  rw [← E.baseChangeCompEqIso_curve_fst g k h w, ← Category.assoc]
  have hi := congrArg (fun f ↦ f.curve.left)
    (E.baseChangeCompEqIso g k h w).inv_hom_id
  change (E.baseChangeCompEqIso g k h w).inv.curve.left ≫
    (E.baseChangeCompEqIso g k h w).hom.curve.left = 𝟙 _ at hi
  rw [hi, Category.id_comp]

/-- The inverse composition comparison retains the original curve coordinate. -/
@[reassoc] theorem baseChangeCompIso_inv_curve_fst (g : T ⟶ S) (k : U ⟶ T) :
    (E.baseChangeCompIso g k).inv.curve.left ≫ pullback.fst E.curve.hom (k ≫ g) =
      pullback.fst (E.baseChange g).curve.hom k ≫ pullback.fst E.curve.hom g := by
  rw [← E.baseChangeCompIso_fst_fst g k, ← Category.assoc]
  have hi := congrArg (fun f ↦ f.curve.left) (E.baseChangeCompIso g k).inv_hom_id
  change (E.baseChangeCompIso g k).inv.curve.left ≫
    (E.baseChangeCompIso g k).hom.curve.left = 𝟙 _ at hi
  rw [hi, Category.id_comp]

/-- The original projection detects full morphisms into a twice pulled-back family. -/
theorem baseChange_twice_hom_ext (g : T ⟶ S) (k : U ⟶ T)
    {D : GeneralizedEllipticCurve U} (a b : D ⟶ (E.baseChange g).baseChange k)
    (h : a.curve.left ≫ pullback.fst _ k ≫ pullback.fst E.curve.hom g =
      b.curve.left ≫ pullback.fst _ k ≫ pullback.fst E.curve.hom g) : a = b := by
  apply baseChange_hom_ext
  apply pullback.hom_ext
  · simpa only [Category.assoc] using h
  · have hw := congrArg (fun f ↦ f ≫ k) (a.curve.w.trans b.curve.w.symm)
    simpa only [baseChange, pullbackCurve, Over.pullback_obj_hom,
      Category.assoc, pullback.condition] using hw

/-- The original projection also detects full morphisms into a threefold pullback. -/
theorem baseChange_thrice_hom_ext (g : T ⟶ S) (k : U ⟶ T) (l : V ⟶ U)
    {D : GeneralizedEllipticCurve V}
    (a b : D ⟶ ((E.baseChange g).baseChange k).baseChange l)
    (h : a.curve.left ≫ pullback.fst _ l ≫ pullback.fst _ k ≫
        pullback.fst E.curve.hom g =
      b.curve.left ≫ pullback.fst _ l ≫ pullback.fst _ k ≫
        pullback.fst E.curve.hom g) : a = b := by
  apply baseChange_twice_hom_ext
  apply pullback.hom_ext
  · simpa only [Category.assoc] using h
  · have hw := congrArg (fun f ↦ f ≫ l ≫ k) (a.curve.w.trans b.curve.w.symm)
    simpa only [baseChange, pullbackCurve, Over.pullback_obj_hom,
      Category.assoc, pullback.condition_assoc, pullback.condition] using hw

end FLT.Mazur.GeneralizedEllipticCurve
