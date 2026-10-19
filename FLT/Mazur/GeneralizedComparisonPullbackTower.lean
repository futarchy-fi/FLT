/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedPresentationRefinement

/-!
# Restricting full comparisons through a tower of test schemes

Pullback of the actual full comparison is compatible with two successive
restrictions, retaining independently named original base maps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T U V : Scheme} (E F : GeneralizedEllipticCurve S)
  (s : T ⟶ S) (p : U ⟶ T) (k : V ⟶ U)
  (v : U ⟶ S) (w : V ⟶ S) (hv : v = p ≫ s) (hw : w = k ≫ v)

/-- Restricting twice keeps exactly the full comparison pulled back along the composite. -/
theorem comparisonPullback_tower (e : E.baseChange s ≅ F.baseChange s) :
    comparisonPullback E F v k w hw (comparisonPullback E F s p v hv e) =
      comparisonPullback E F s (k ≫ p) w
        (hw.trans ((congrArg (k ≫ ·) hv).trans (Category.assoc k p s).symm)) e := by
  let A := E.baseChangeCompEqIso s (k ≫ p) w
    (hw.trans ((congrArg (k ≫ ·) hv).trans (Category.assoc k p s).symm))
  let B := F.baseChangeCompEqIso s (k ≫ p) w
    (hw.trans ((congrArg (k ≫ ·) hv).trans (Category.assoc k p s).symm))
  let C := E.baseChangeCompEqIso v k w hw
  let D := F.baseChangeCompEqIso v k w hw
  let P := (baseChangeFunctor k).mapIso (E.baseChangeCompEqIso s p v hv)
  let Q := (baseChangeFunctor k).mapIso (F.baseChangeCompEqIso s p v hv)
  have hE : C.hom ≫ P.hom = A.hom ≫ ((E.baseChange s).baseChangeCompIso p k).hom :=
    (E.baseChangeCompEqIso_assoc s p k v w hv hw).symm
  have hF : D.hom ≫ Q.hom = B.hom ≫ ((F.baseChange s).baseChangeCompIso p k).hom :=
    (F.baseChangeCompEqIso_assoc s p k v w hv hw).symm
  have hn := (baseChangeComp p k).hom.naturality e.hom
  change baseChangeMap (k ≫ p) e.hom ≫ ((F.baseChange s).baseChangeCompIso p k).hom =
    ((E.baseChange s).baseChangeCompIso p k).hom ≫
      baseChangeMap k (baseChangeMap p e.hom) at hn
  simp only [comparisonPullback, Functor.mapIso_trans, Functor.mapIso_symm]
  apply Iso.ext
  apply (cancel_mono (D.hom ≫ Q.hom)).mp
  change (C.hom ≫ (P.hom ≫ baseChangeMap k (baseChangeMap p e.hom) ≫ Q.inv) ≫ D.inv) ≫
    (D.hom ≫ Q.hom) = (A.hom ≫ baseChangeMap (k ≫ p) e.hom ≫ B.inv) ≫ _
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hF]
  simp only [Iso.inv_hom_id_assoc]
  rw [← Category.assoc C.hom, hE]
  simp only [Category.assoc]
  rw [hn]

end FLT.Mazur.GeneralizedEllipticCurve
