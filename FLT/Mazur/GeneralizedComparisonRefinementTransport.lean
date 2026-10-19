/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedPresentationBaseChangeRefinement

/-!
# Full comparison refinement through original-family presentations

The refinement identity for concrete models transports through coherent
presentations to the original full families.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T U V : Scheme} (s : T ⟶ S) (p : V ⟶ T) (k : U ⟶ S) (t : V ⟶ U)
  (v : V ⟶ S) (hp : v = p ≫ s) (ht : v = t ≫ k)
  {D H E F : GeneralizedEllipticCurve S} {D' H' E' F' : GeneralizedEllipticCurve U}
  (a : D ≅ E) (b : H ≅ F) (a' : D' ≅ E') (b' : H' ≅ F')
  (r : D' ≅ D.baseChange k) (q : H' ≅ H.baseChange k)
  (x : E' ≅ E.baseChange k) (y : F' ≅ F.baseChange k)
  (ha : a' ≪≫ x = r ≪≫ (baseChangeFunctor k).mapIso a)
  (hb : b' ≪≫ y = q ≪≫ (baseChangeFunctor k).mapIso b)
  (e : D.baseChange s ≅ H.baseChange s) (e' : D'.baseChange t ≅ H'.baseChange t)
  (he : comparisonPullback D H s p v hp e =
    D.baseChangeCompEqIso k t v ht ≪≫ ((baseChangeFunctor t).mapIso r).symm ≪≫ e' ≪≫
      (baseChangeFunctor t).mapIso q ≪≫ (H.baseChangeCompEqIso k t v ht).symm)

include ha hb he in
/-- The original full families inherit the concrete comparison's refinement identity. -/
theorem comparisonPullback_refine_transport :
    comparisonPullback E F s p v hp
      (((baseChangeFunctor s).mapIso a).symm ≪≫ e ≪≫ (baseChangeFunctor s).mapIso b) =
    E.baseChangeCompEqIso k t v ht ≪≫ ((baseChangeFunctor t).mapIso x).symm ≪≫
      (((baseChangeFunctor t).mapIso a').symm ≪≫ e' ≪≫ (baseChangeFunctor t).mapIso b') ≪≫
        (baseChangeFunctor t).mapIso y ≪≫ (F.baseChangeCompEqIso k t v ht).symm := by
  rw [comparisonPullback_natural, he]
  have hD := presentationBaseChange_refine k t v ht a a' r x ha
  have hH := presentationBaseChange_refine k t v ht b b' q y hb
  calc
    _ = ((baseChangeFunctor t).mapIso r ≪≫ (D.baseChangeCompEqIso k t v ht).symm ≪≫
        (baseChangeFunctor v).mapIso a).symm ≪≫ e' ≪≫
          ((baseChangeFunctor t).mapIso q ≪≫ (H.baseChangeCompEqIso k t v ht).symm ≪≫
            (baseChangeFunctor v).mapIso b) := by
      apply Iso.ext
      simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Category.assoc]
    _ = _ := by
      rw [← hD, ← hH]
      apply Iso.ext
      simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Category.assoc]

end FLT.Mazur.GeneralizedEllipticCurve
