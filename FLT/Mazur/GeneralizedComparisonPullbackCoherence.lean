/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveBaseChangeCompEq

/-!
# Pulling back full comparisons through coherent presentations

A comparison on a parameter scheme pulls back to the original full families.
Coherent coefficient presentations identify it with the specialized comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.isDefEq.respectTransparency false
variable {S T U : Scheme} (E F : GeneralizedEllipticCurve S)
  (s : T ⟶ S) (p : U ⟶ T) (t : U ⟶ S) (ht : t = p ≫ s)

/-- Pull back the entire comparison, retaining the prescribed original base maps. -/
def comparisonPullback (e : E.baseChange s ≅ F.baseChange s) :
    E.baseChange t ≅ F.baseChange t :=
  E.baseChangeCompEqIso s p t ht ≪≫ (baseChangeFunctor p).mapIso e ≪≫
    (F.baseChangeCompEqIso s p t ht).symm

/-- Coherent presentation squares identify the pulled-back full comparison. -/
theorem comparisonPullback_conjugate
    {D H : GeneralizedEllipticCurve T} {D' H' : GeneralizedEllipticCurve U}
    (a : D ≅ E.baseChange s) (b : H ≅ F.baseChange s)
    (c : D' ≅ E.baseChange t) (d : H' ≅ F.baseChange t)
    (r : D' ≅ D.baseChange p) (q : H' ≅ H.baseChange p)
    (e : D ≅ H) (e' : D' ≅ H')
    (hc : c.hom ≫ (E.baseChangeCompEqIso s p t ht).hom =
      r.hom ≫ baseChangeMap p a.hom)
    (hd : d.hom ≫ (F.baseChangeCompEqIso s p t ht).hom =
      q.hom ≫ baseChangeMap p b.hom)
    (he : r.hom ≫ baseChangeMap p e.hom = e'.hom ≫ q.hom) :
    comparisonPullback E F s p t ht (a.symm ≪≫ e ≪≫ b) = c.symm ≪≫ e' ≪≫ d := by
  let A := (baseChangeFunctor p).mapIso a
  let B := (baseChangeFunctor p).mapIso b
  have hc' := congrArg (fun z ↦ c.inv ≫ z ≫ A.inv) hc
  have hd' := congrArg (fun z ↦ z ≫ (F.baseChangeCompEqIso s p t ht).inv) hd
  change c.inv ≫ (c.hom ≫ _) ≫ A.inv = c.inv ≫ (r.hom ≫ A.hom) ≫ A.inv at hc'
  change (d.hom ≫ _) ≫ _ = (q.hom ≫ B.hom) ≫ _ at hd'
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
    Category.comp_id] at hc' hd'
  apply Iso.ext
  simp only [comparisonPullback, CategoryTheory.Functor.mapIso_trans,
    CategoryTheory.Functor.mapIso_symm, Iso.trans_hom, Iso.symm_hom]
  change (E.baseChangeCompEqIso s p t ht).hom ≫
    (A.inv ≫ baseChangeMap p e.hom ≫ B.hom) ≫
      (F.baseChangeCompEqIso s p t ht).inv = c.inv ≫ e'.hom ≫ d.hom
  rw [← Category.assoc, ← Category.assoc, hc']
  simp only [Category.assoc]
  rw [← Category.assoc r.hom, he]
  simp only [Category.assoc]
  rw [← hd']

end FLT.Mazur.GeneralizedEllipticCurve
