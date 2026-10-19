/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedComparisonPullbackNaturality

/-!
# Refinement squares for presentations on a parameter scheme

A coherent presentation square on the coefficient base stays coherent after
restriction to any parameter scheme, with independently named base maps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T U : Scheme} (k : T ⟶ S) (s : U ⟶ T) (t : U ⟶ S) (ht : t = s ≫ k)
  {D E : GeneralizedEllipticCurve S} {D' E' : GeneralizedEllipticCurve T}
  (a : D ≅ E) (a' : D' ≅ E') (r : D' ≅ D.baseChange k) (v : E' ≅ E.baseChange k)
  (h : a' ≪≫ v = r ≪≫ (baseChangeFunctor k).mapIso a)

include h in
/-- Coherent full presentations remain coherent on arbitrary parameter schemes. -/
theorem presentationBaseChange_refine :
    (baseChangeFunctor s).mapIso a' ≪≫ (baseChangeFunctor s).mapIso v ≪≫
      (E.baseChangeCompEqIso k s t ht).symm =
    (baseChangeFunctor s).mapIso r ≪≫ (D.baseChangeCompEqIso k s t ht).symm ≪≫
      (baseChangeFunctor t).mapIso a := by
  rw [← Iso.trans_assoc, ← Functor.mapIso_trans, h, Functor.mapIso_trans]
  rw [Iso.trans_assoc]
  congr 1
  apply Iso.ext
  apply (Iso.comp_inv_eq _).mpr
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  change baseChangeMap s (baseChangeMap k a.hom) =
    (D.baseChangeCompEqIso k s t ht).inv ≫ baseChangeMap t a.hom ≫
      (E.baseChangeCompEqIso k s t ht).hom
  rw [baseChangeCompEqIso_natural k s t ht a.hom, Iso.inv_hom_id_assoc]

end FLT.Mazur.GeneralizedEllipticCurve
