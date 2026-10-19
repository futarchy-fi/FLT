/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedComparisonPullbackNaturality

/-!
# Refinement of full presentations through a coefficient base

Coherent coefficient presentations stay coherent after transport to an
original family over an intermediate base. Equal base maps are retained.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T U V : Scheme} (E : GeneralizedEllipticCurve S)
  (u : T ⟶ S) (q : U ⟶ T) (k : V ⟶ U)
  (v : U ⟶ S) (w : V ⟶ S) (hv : v = q ≫ u) (hw : w = k ≫ v)

/-- Threefold pullback coherence retains arbitrary names for the composite base maps. -/
theorem baseChangeCompEqIso_assoc :
    (E.baseChangeCompEqIso u (k ≫ q) w
      (hw.trans ((congrArg (k ≫ ·) hv).trans (Category.assoc k q u).symm))).hom ≫
        ((E.baseChange u).baseChangeCompIso q k).hom =
      (E.baseChangeCompEqIso v k w hw).hom ≫
        baseChangeMap k (E.baseChangeCompEqIso u q v hv).hom := by
  subst v
  subst w
  change (baseChangeCongr (Category.assoc k q u).symm).hom.app E ≫
    (E.baseChangeCompIso u (k ≫ q)).hom ≫
      ((E.baseChange u).baseChangeCompIso q k).hom =
    (E.baseChangeCompIso (q ≫ u) k).hom ≫ baseChangeMap k (E.baseChangeCompIso u q).hom
  rw [baseChange_assoc]
  change (baseChangeCongr (Category.assoc k q u)).inv.app E ≫
    (baseChangeCongr (Category.assoc k q u)).hom.app E ≫ _ = _
  rw [Iso.inv_hom_id_app_assoc]

variable {F : GeneralizedEllipticCurve T} {D : GeneralizedEllipticCurve U}
  {D' : GeneralizedEllipticCurve V}

/-- A full coefficient presentation gives a presentation of the original family. -/
def presentationThroughBase (a : E.baseChange u ≅ F) (e : D ≅ E.baseChange v) :
    D ≅ F.baseChange q :=
  e ≪≫ E.baseChangeCompEqIso u q v hv ≪≫ (baseChangeFunctor q).mapIso a

/-- Refinement of a coefficient presentation commutes with its original-family transport. -/
theorem presentationThroughBase_refine
    (a : E.baseChange u ≅ F) (e : D ≅ E.baseChange v) (d : D' ≅ E.baseChange w)
    (r : D' ≅ D.baseChange k)
    (hc : d.hom ≫ (E.baseChangeCompEqIso v k w hw).hom =
      r.hom ≫ baseChangeMap k e.hom) :
    (presentationThroughBase E u (k ≫ q) w
      (hw.trans ((congrArg (k ≫ ·) hv).trans (Category.assoc k q u).symm)) a d).hom ≫
        (F.baseChangeCompIso q k).hom =
      r.hom ≫ baseChangeMap k (presentationThroughBase E u q v hv a e).hom := by
  have hn := (baseChangeComp q k).hom.naturality a.hom
  change baseChangeMap (k ≫ q) a.hom ≫ (F.baseChangeCompIso q k).hom =
    ((E.baseChange u).baseChangeCompIso q k).hom ≫
      baseChangeMap k (baseChangeMap q a.hom) at hn
  simp only [presentationThroughBase, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc]
  change d.hom ≫ (E.baseChangeCompEqIso u (k ≫ q) w _).hom ≫
    baseChangeMap (k ≫ q) a.hom ≫ (F.baseChangeCompIso q k).hom =
      r.hom ≫ baseChangeMap k
        (e.hom ≫ (E.baseChangeCompEqIso u q v hv).hom ≫ baseChangeMap q a.hom)
  rw [hn, ← Category.assoc _ ((E.baseChange u).baseChangeCompIso q k).hom,
    baseChangeCompEqIso_assoc E u q k v w hv hw]
  simp only [Category.assoc]
  rw [← Category.assoc d.hom, hc]
  change _ = r.hom ≫ (baseChangeFunctor k).map
    (e.hom ≫ (E.baseChangeCompEqIso u q v hv).hom ≫ baseChangeMap q a.hom)
  simp only [Functor.map_comp, Category.assoc]
  rfl

end FLT.Mazur.GeneralizedEllipticCurve
