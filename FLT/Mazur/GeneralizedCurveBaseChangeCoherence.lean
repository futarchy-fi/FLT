/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveBaseChangeIso
public import FLT.Mazur.OverPullbackCoherence

/-!
# Coherence of generalized-curve base change

Unit and associativity identities hold in the full DR category, as checked
on the canonical projections of the underlying curves.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.OverPullbackCoherence
namespace FLT.Mazur.GeneralizedEllipticCurve
variable {S T U V : Scheme}

/-- Equal base maps induce the same base-change functor. -/
def baseChangeCongr {f g : T ⟶ S} (e : f = g) :
    baseChangeFunctor f ≅ baseChangeFunctor g := eqToIso (congrArg baseChangeFunctor e)

/-- Equality comparison preserves the original curve projection. -/
@[reassoc (attr := simp)]
theorem baseChangeCongr_fst {f g : T ⟶ S} (e : f = g)
    (E : GeneralizedEllipticCurve S) :
    ((baseChangeCongr e).hom.app E).curve.left ≫ pullback.fst E.curve.hom g =
      pullback.fst E.curve.hom f := by
  subst g
  change (𝟙 _) ≫ _ = _
  exact Category.id_comp _

/-- The identity comparison has the canonical curve projection. -/
@[simp]
theorem baseChangeIdIso_left (E : GeneralizedEllipticCurve S) :
    E.baseChangeIdIso.hom.curve.left = pullback.fst E.curve.hom (𝟙 S) :=
  id_left E.curve

/-- The composition comparison retains the projection to the original curve. -/
@[reassoc (attr := simp)]
theorem baseChangeCompIso_fst_fst (E : GeneralizedEllipticCurve S)
    (g : T ⟶ S) (h : U ⟶ T) :
    (E.baseChangeCompIso g h).hom.curve.left ≫
      pullback.fst (E.baseChange g).curve.hom h ≫ pullback.fst E.curve.hom g =
        pullback.fst E.curve.hom (h ≫ g) := comp_left_fst_fst g h E.curve

/-- Base change of a morphism retains its original curve projection. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_fst (g : T ⟶ S) {E F : GeneralizedEllipticCurve S} (f : E ⟶ F) :
    (baseChangeMap g f).curve.left ≫ pullback.fst F.curve.hom g =
      pullback.fst E.curve.hom g ≫ f.curve.left := by
  simp [baseChangeMap, Over.pullback_map_left]

/-- A morphism into a base change is determined by its original curve projection. -/
theorem baseChange_hom_ext {E : GeneralizedEllipticCurve S}
    {D : GeneralizedEllipticCurve T} (g : T ⟶ S) (f h : D ⟶ E.baseChange g)
    (e : f.curve.left ≫ pullback.fst E.curve.hom g =
      h.curve.left ≫ pullback.fst E.curve.hom g) : f = h := by
  apply forgetCurve.map_injective
  apply (Over.forget T).map_injective
  apply pullback.hom_ext e
  exact f.curve.w.trans h.curve.w.symm

/-- Pullback along an identity after base change satisfies the unit identity. -/
theorem baseChange_comp_id (E : GeneralizedEllipticCurve S) (g : T ⟶ S) :
    (E.baseChangeCompIso g (𝟙 T)).hom ≫ (E.baseChange g).baseChangeIdIso.hom =
      (baseChangeCongr (Category.id_comp g)).hom.app E := by
  apply baseChange_hom_ext
  change (E.baseChangeCompIso g (𝟙 T)).hom.curve.left ≫
    (E.baseChange g).baseChangeIdIso.hom.curve.left ≫ _ = _
  rw [baseChangeIdIso_left]
  exact (E.baseChangeCompIso_fst_fst g (𝟙 T)).trans
    (baseChangeCongr_fst (Category.id_comp g) E).symm

/-- Pullback of the identity comparison satisfies the other unit identity. -/
theorem baseChange_id_comp (E : GeneralizedEllipticCurve S) (g : T ⟶ S) :
    (E.baseChangeCompIso (𝟙 S) g).hom ≫ baseChangeMap g E.baseChangeIdIso.hom =
      (baseChangeCongr (Category.comp_id g)).hom.app E := by
  apply baseChange_hom_ext
  change (E.baseChangeCompIso (𝟙 S) g).hom.curve.left ≫
    (baseChangeMap g E.baseChangeIdIso.hom).curve.left ≫ _ = _
  rw [baseChangeMap_fst, baseChangeIdIso_left]
  exact (E.baseChangeCompIso_fst_fst (𝟙 S) g).trans
    (baseChangeCongr_fst (Category.comp_id g) E).symm

/-- The two threefold comparison paths agree in the full DR category. -/
theorem baseChange_assoc (E : GeneralizedEllipticCurve S)
    (g : T ⟶ S) (h : U ⟶ T) (k : V ⟶ U) :
    (E.baseChangeCompIso g (k ≫ h)).hom ≫ ((E.baseChange g).baseChangeCompIso h k).hom =
      (baseChangeCongr (Category.assoc k h g)).hom.app E ≫
        (E.baseChangeCompIso (h ≫ g) k).hom ≫
          baseChangeMap k (E.baseChangeCompIso g h).hom := by
  let a := (E.baseChangeCompIso g (k ≫ h)).hom ≫
    ((E.baseChange g).baseChangeCompIso h k).hom
  let b := (baseChangeCongr (Category.assoc k h g)).hom.app E ≫
    (E.baseChangeCompIso (h ≫ g) k).hom ≫ baseChangeMap k (E.baseChangeCompIso g h).hom
  have hw := a.curve.w.trans b.curve.w.symm
  apply forgetCurve.map_injective
  apply (Over.forget V).map_injective
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · change (E.baseChangeCompIso g (k ≫ h)).hom.curve.left ≫
          ((E.baseChange g).baseChangeCompIso h k).hom.curve.left ≫
          pullback.fst _ k ≫ pullback.fst _ h ≫ pullback.fst _ g =
            ((baseChangeCongr (Category.assoc k h g)).hom.app E).curve.left ≫
              (E.baseChangeCompIso (h ≫ g) k).hom.curve.left ≫
              (baseChangeMap k (E.baseChangeCompIso g h).hom).curve.left ≫
              pullback.fst _ k ≫ pullback.fst _ h ≫ pullback.fst _ g
        simp only [baseChangeMap_fst_assoc, baseChangeCompIso_fst_fst_assoc,
          baseChangeCompIso_fst_fst, baseChangeCongr_fst]
      · change (a.curve.left ≫ pullback.fst _ k ≫ pullback.fst _ h) ≫
          pullback.snd E.curve.hom g =
            (b.curve.left ≫ pullback.fst _ k ≫ pullback.fst _ h) ≫ pullback.snd E.curve.hom g
        simpa only [baseChange, pullbackCurve, Over.pullback_obj_hom,
          Category.assoc, pullback.condition_assoc, pullback.condition] using
          congrArg (fun z ↦ z ≫ k ≫ h) hw
    · change (a.curve.left ≫ pullback.fst _ k) ≫ pullback.snd _ h =
        (b.curve.left ≫ pullback.fst _ k) ≫ pullback.snd _ h
      simpa only [baseChange, pullbackCurve, Over.pullback_obj_hom,
        Category.assoc, pullback.condition] using congrArg (fun z ↦ z ≫ k) hw
  · exact hw

end FLT.Mazur.GeneralizedEllipticCurve
