/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedDescentCharts
public import FLT.Mazur.ModuleSheafGluing

/-!
# Restriction coherence for closed descent charts

Canonical comparisons identify successive open restrictions with direct
restriction. Their section formulas control the chart comparisons on nested
ambient opens.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules

universe u

namespace FLT.Mazur.FCurve.CoherentDevissage.ClosedDescentCharts

variable {X Y : Scheme.{u}}

/-- Restriction evaluates a module morphism on image opens. -/
lemma restrictMap_app (g : X ⟶ Y) [IsOpenImmersion g] {P Q : Y.Modules}
    (a : P ⟶ Q) (T : X.Opens) :
    ((restrictFunctor g).map a).app T = a.app (g ''ᵁ T) := rfl

/-- The canonical comparison from a nested restriction to a direct restriction. -/
def nestedRestriction {V W : X.Opens} (h : W ≤ V) :
    restrictFunctor V.ι ⋙ restrictFunctor (X.homOfLE h) ≅ restrictFunctor W.ι :=
  (restrictFunctorComp (X.homOfLE h) V.ι).symm ≪≫
    restrictFunctorCongr (X.homOfLE_ι h)

/-- On sections the nested comparison is the canonical equality of image opens. -/
lemma nestedRestriction_hom_app (P : X.Modules) {V W : X.Opens} (h : W ≤ V)
    (T : W.toScheme.Opens) :
    ((nestedRestriction h).hom.app P).app T =
      P.presheaf.map (eqToHom (show W.ι ''ᵁ T = V.ι ''ᵁ (X.homOfLE h ''ᵁ T) by
        simp only [← Scheme.Hom.comp_image, X.homOfLE_ι])).op := by
  simp only [nestedRestriction, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Hom.comp_app, restrictFunctorComp_inv_app_app, restrictFunctorCongr_hom_app_app,
    ← Functor.map_comp]
  congr 1

/-- The inverse nested comparison uses the reverse equality of image opens. -/
lemma nestedRestriction_inv_app (P : X.Modules) {V W : X.Opens} (h : W ≤ V)
    (T : W.toScheme.Opens) :
    ((nestedRestriction h).inv.app P).app T =
      P.presheaf.map (eqToHom (show V.ι ''ᵁ (X.homOfLE h ''ᵁ T) = W.ι ''ᵁ T by
        simp only [← Scheme.Hom.comp_image, X.homOfLE_ι])).op := by
  simp only [nestedRestriction, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Hom.comp_app, restrictFunctorComp_hom_app_app, restrictFunctorCongr_inv_app_app,
    ← Functor.map_comp]
  congr 1

/-- Reversing equality of immersions reverses the restriction comparison. -/
lemma restrictCongr_symm_app {f g : X ⟶ Y} (h : f = g)
    [IsOpenImmersion f] [IsOpenImmersion g] (P : Y.Modules) :
    (restrictFunctorCongr h.symm).hom.app P = (restrictFunctorCongr h).inv.app P := by
  apply Scheme.Modules.hom_ext
  intro T
  simp only [restrictFunctorCongr_hom_app_app, restrictFunctorCongr_inv_app_app]

/-- Subopen comparison is restriction conjugated by the canonical nested comparisons. -/
lemma subopenComparison_eq {P : Y.Modules} [P.IsFinitePresentation]
    (I : Y.IdealSheafData) (hP : IdealKilled I P) (U : Y.affineOpens)
    (V : Y.Opens) (h : V ≤ U.1) :
    subopenComparison I P hP U V h =
      ((nestedRestriction h).app _).symm ≪≫
        (restrictFunctor (Y.homOfLE h)).mapIso (extensionComparison I P hP U) ≪≫
          (nestedRestriction h).app P := by
  apply Iso.ext
  simp only [subopenComparison, nestedRestriction, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv, NatTrans.comp_app,
    Category.assoc]
  congr 1

/-- Inverse image commutes with the inclusion between two ambient opens. -/
lemma nestedRestriction_preimage (f : X ⟶ Y) {V W : Y.Opens} (h : W ≤ V)
    (T : W.toScheme.Opens) :
    X.homOfLE (f.preimage_mono h) ''ᵁ ((f ∣_ W) ⁻¹ᵁ T) =
      (f ∣_ V) ⁻¹ᵁ (Y.homOfLE h ''ᵁ T) := by
  apply (f ⁻¹ᵁ V).ι.image_injective
  simp only [← Scheme.Hom.comp_image, Scheme.homOfLE_ι,
    image_morphismRestrict_preimage]

/-- Base change for the inclusion of one ambient open in another. -/
def nestedPushforwardRestriction (f : X ⟶ Y) {V W : Y.Opens} (h : W ≤ V) :
    pushforward (f ∣_ V) ⋙ restrictFunctor (Y.homOfLE h) ≅
      restrictFunctor (X.homOfLE (f.preimage_mono h)) ⋙ pushforward (f ∣_ W) := by
  have : ((Y.homOfLE h).opensFunctor ⋙ Opens.map (f ∣_ V).base).IsContinuous
      (Opens.grothendieckTopology W.toScheme)
      (Opens.grothendieckTopology (f ⁻¹ᵁ V).toScheme) :=
    Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology V.toScheme) _
  have : (Opens.map (f ∣_ W).base ⋙
      (X.homOfLE (f.preimage_mono h)).opensFunctor).IsContinuous
      (Opens.grothendieckTopology W.toScheme)
      (Opens.grothendieckTopology (f ⁻¹ᵁ V).toScheme) :=
    Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology (f ⁻¹ᵁ W).toScheme) _
  refine SheafOfModules.pushforwardComp _ _ ≪≫ ?_ ≪≫
    (SheafOfModules.pushforwardComp _ _).symm
  refine SheafOfModules.pushforwardCongr₂ _ ?_ ?_
  · exact NatIso.ofComponents
      (fun T ↦ eqToIso (nestedRestriction_preimage f h T)) (by cat_disch)
  · ext T x
    simp only [Scheme.Hom.appIso_homOfLE_inv]
    change ((f ⁻¹ᵁ V).toScheme.presheaf.map
      (eqToHom (nestedRestriction_preimage f h T.unop)).op)
        ((f ∣_ V).app (Y.homOfLE h ''ᵁ T.unop)
          (Y.presheaf.map _ x)) =
      X.presheaf.map _ ((f ∣_ W).app T.unop x)
    simp only [morphismRestrict_app, CommRingCat.comp_apply,
      Scheme.Opens.toScheme_presheaf_map]
    change X.presheaf.map _ (X.presheaf.map _
      (f.app (V.ι ''ᵁ (Y.homOfLE h ''ᵁ T.unop)) (Y.presheaf.map _ x))) =
        X.presheaf.map _ (X.presheaf.map _ (f.app (W.ι ''ᵁ T.unop) x))
    simp only [← ConcreteCategory.comp_apply]
    erw [f.naturality]
    simp only [Category.assoc, ← Functor.map_comp]
    congr 2

/-- The nested base-change comparison on sections. -/
lemma nestedPushforwardRestriction_hom_app (f : X ⟶ Y) {V W : Y.Opens}
    (h : W ≤ V) (P : (f ⁻¹ᵁ V).toScheme.Modules) (T : W.toScheme.Opens) :
    ((nestedPushforwardRestriction f h).hom.app P).app T =
      P.presheaf.map (eqToHom (nestedRestriction_preimage f h T)).op := rfl

/-- Base change along nested opens agrees with base change along the outer inclusion. -/
lemma closedPushforwardRestriction_nested (f : X ⟶ Y) {V W : Y.Opens}
    (h : W ≤ V) (P : X.Modules) :
    (restrictFunctor (Y.homOfLE h)).map ((closedPushforwardRestriction f V).hom.app P) ≫
        (nestedPushforwardRestriction f h).hom.app (P.restrict (f ⁻¹ᵁ V).ι) ≫
          (pushforward (f ∣_ W)).map ((nestedRestriction (f.preimage_mono h)).hom.app P) =
      (nestedRestriction h).hom.app ((pushforward f).obj P) ≫
        (closedPushforwardRestriction f W).hom.app P := by
  apply Scheme.Modules.hom_ext
  intro T
  simp only [Hom.comp_app, restrictMap_app, closedPushforwardRestriction_hom_app,
    nestedPushforwardRestriction_hom_app, pushforward_map_app, nestedRestriction_hom_app,
    restrict_map, pushforward_obj_presheaf_map, ← Functor.map_comp]
  congr 1

set_option maxHeartbeats 400000 in
-- Section transports require extra reduction of restricted module structures.
/-- Restriction of any comparison is coherent on a chain of three opens. -/
lemma nestedComparison {P Q : Y.Modules} {U V W : Y.Opens}
    (E : P.restrict U.ι ≅ Q.restrict U.ι) (hV : V ≤ U) (hWV : W ≤ V) :
    (restrictFunctor (Y.homOfLE hWV)).mapIso
        (((nestedRestriction hV).app P).symm ≪≫
          (restrictFunctor (Y.homOfLE hV)).mapIso E ≪≫ (nestedRestriction hV).app Q) ≪≫
        (nestedRestriction hWV).app Q =
      (nestedRestriction hWV).app P ≪≫
        ((nestedRestriction (hWV.trans hV)).app P).symm ≪≫
          (restrictFunctor (Y.homOfLE (hWV.trans hV))).mapIso E ≪≫
            (nestedRestriction (hWV.trans hV)).app Q := by
  apply Iso.ext
  apply Scheme.Modules.hom_ext
  intro T
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Hom.comp_app,
    restrictMap_app, Iso.app_hom, Iso.app_inv,
    nestedRestriction_hom_app, nestedRestriction_inv_app]
  have e : Y.homOfLE hV ''ᵁ (Y.homOfLE hWV ''ᵁ T) =
      Y.homOfLE (hWV.trans hV) ''ᵁ T := by
    simp only [← Scheme.Hom.comp_image, Scheme.homOfLE_homOfLE]
  have hn := E.hom.mapPresheaf.naturality (eqToHom e).op
  have e₁ : V.ι ''ᵁ (Y.homOfLE hWV ''ᵁ T) =
      U.ι ''ᵁ (Y.homOfLE (hWV.trans hV) ''ᵁ T) := by
    simp only [← Scheme.Hom.comp_image, Scheme.homOfLE_ι]
  have e₂ : U.ι ''ᵁ (Y.homOfLE hV ''ᵁ (Y.homOfLE hWV ''ᵁ T)) = W.ι ''ᵁ T := by
    simp only [← Scheme.Hom.comp_image, Scheme.homOfLE_homOfLE, Scheme.homOfLE_ι]
  apply (cancel_epi (P.presheaf.map (eqToHom e₁).op)).mp
  apply (cancel_mono (Q.presheaf.map (eqToHom e₂).op)).mp
  simp only [Category.assoc, ← Functor.map_comp, ← Functor.map_comp_assoc,
    ← op_comp, eqToHom_trans, eqToHom_refl, op_id]
  erw [Q.presheaf.map_id, P.presheaf.map_id]
  erw [Category.comp_id]
  erw [Category.id_comp]
  change P.presheaf.map ((U.ι.opensFunctor).map (eqToHom e)).op ≫
      E.hom.app (Y.homOfLE hV ''ᵁ (Y.homOfLE hWV ''ᵁ T)) =
    E.hom.app (Y.homOfLE (hWV.trans hV) ''ᵁ T) ≫
      Q.presheaf.map ((U.ι.opensFunctor).map (eqToHom e)).op at hn
  have hn' := congrArg (fun a ↦
    (P.restrictAppIso U.ι (Y.homOfLE (hWV.trans hV) ''ᵁ T)).inv ≫ a ≫
      (Q.restrictAppIso U.ι (Y.homOfLE hV ''ᵁ (Y.homOfLE hWV ''ᵁ T))).hom) hn
  simp only [restrictAppIso, Iso.refl_inv, Iso.refl_hom, eqToHom_map] at hn'
  erw [Category.id_comp, Category.id_comp, Category.comp_id, Category.comp_id] at hn'
  exact hn'

/-- Restricting the ambient comparison further agrees with the direct comparison. -/
lemma subopenComparison_nested (I : Y.IdealSheafData) (P : Y.Modules)
    [P.IsFinitePresentation] (hP : IdealKilled I P) (U : Y.affineOpens)
    (V W : Y.Opens) (hV : V ≤ U.1) (hWV : W ≤ V) :
    (restrictFunctor (Y.homOfLE hWV)).mapIso (subopenComparison I P hP U V hV) ≪≫
        (nestedRestriction hWV).app P =
      (nestedRestriction hWV).app _ ≪≫
        subopenComparison I P hP U W (hWV.trans hV) := by
  simpa only [subopenComparison_eq] using
    nestedComparison (extensionComparison I P hP U) hV hWV

/-- The pushforward comparisons commute with further restriction. -/
lemma comparisonOn_nested (I : Y.IdealSheafData) (P : Y.Modules)
    [P.IsFinitePresentation] (hP : IdealKilled I P) (U : Y.affineOpens)
    (V W : Y.Opens) (hV : V ≤ U.1) (hWV : W ≤ V) :
    (restrictFunctor (Y.homOfLE hWV)).map (comparisonOn I P hP U V hV).hom ≫
        (nestedRestriction hWV).hom.app P =
      (nestedPushforwardRestriction I.subschemeι hWV).hom.app (chartOn I P hP U V) ≫
        (pushforward (I.subschemeι ∣_ W)).map
          ((nestedRestriction (I.subschemeι.preimage_mono hWV)).hom.app
            (chartExtension I P hP U)) ≫
          (comparisonOn I P hP U W (hWV.trans hV)).hom := by
  have hs := congrArg Iso.hom (subopenComparison_nested I P hP U V W hV hWV)
  have hb := closedPushforwardRestriction_nested I.subschemeι hWV (chartExtension I P hP U)
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom] at hs
  apply (cancel_epi ((restrictFunctor (Y.homOfLE hWV)).map
    ((closedPushforwardRestriction I.subschemeι V).hom.app (chartExtension I P hP U)))).mp
  simp only [comparisonOn, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.map_comp]
  simp only [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
    Category.id_comp]
  rw [← Category.assoc] at hb
  rw [hb]
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using hs

/-- Lifted transitions commute with restriction to any smaller ambient open. -/
lemma transitionOn_nested (I : Y.IdealSheafData) (P : Y.Modules)
    [P.IsFinitePresentation] (hP : IdealKilled I P) (U U' : Y.affineOpens)
    (V W : Y.Opens) (hV : V ≤ U.1) (hV' : V ≤ U'.1) (hWV : W ≤ V) :
    (restrictFunctor (I.subscheme.homOfLE (I.subschemeι.preimage_mono hWV))).map
        (transitionOn I P hP U U' V hV hV').hom ≫
          (nestedRestriction (I.subschemeι.preimage_mono hWV)).hom.app
            (chartExtension I P hP U') =
      (nestedRestriction (I.subschemeι.preimage_mono hWV)).hom.app
          (chartExtension I P hP U) ≫
        (transitionOn I P hP U U' W (hWV.trans hV) (hWV.trans hV')).hom := by
  apply (pushforward (I.subschemeι ∣_ W)).map_injective
  simp only [Functor.map_comp]
  apply (cancel_epi ((nestedPushforwardRestriction I.subschemeι hWV).hom.app
    (chartOn I P hP U V))).mp
  apply (cancel_mono (comparisonOn I P hP U' W (hWV.trans hV')).hom).mp
  have hn := (nestedPushforwardRestriction I.subschemeι hWV).hom.naturality
    (transitionOn I P hP U U' V hV hV').hom
  have hv := congrArg Iso.hom (transitionOn_pushforward I P hP U U' V hV hV')
  have hw := congrArg Iso.hom
    (transitionOn_pushforward I P hP U U' W (hWV.trans hV) (hWV.trans hV'))
  simp only [Functor.comp_map] at hn
  simp only [Category.assoc]
  rw [← reassoc_of% hn, ← comparisonOn_nested I P hP U' V W hV' hWV]
  simp only [Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom] at hv hw
  rw [hv, hw]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id, Category.comp_id]
  exact comparisonOn_nested I P hP U V W hV hWV

/-- Lifted ambient morphisms commute with restriction to smaller opens. -/
lemma mapOn_nested (I : Y.IdealSheafData) {P Q : Y.Modules}
    [P.IsFinitePresentation] [Q.IsFinitePresentation]
    (hP : IdealKilled I P) (hQ : IdealKilled I Q) (a : P ⟶ Q)
    (U : Y.affineOpens) (V W : Y.Opens) (hV : V ≤ U.1) (hWV : W ≤ V) :
    (restrictFunctor (I.subscheme.homOfLE (I.subschemeι.preimage_mono hWV))).map
        (mapOn I hP hQ a U V hV) ≫
          (nestedRestriction (I.subschemeι.preimage_mono hWV)).hom.app
            (chartExtension I Q hQ U) =
      (nestedRestriction (I.subschemeι.preimage_mono hWV)).hom.app
          (chartExtension I P hP U) ≫
        mapOn I hP hQ a U W (hWV.trans hV) := by
  apply (pushforward (I.subschemeι ∣_ W)).map_injective
  simp only [Functor.map_comp]
  apply (cancel_epi ((nestedPushforwardRestriction I.subschemeι hWV).hom.app
    (chartOn I P hP U V))).mp
  apply (cancel_mono (comparisonOn I Q hQ U W (hWV.trans hV)).hom).mp
  have hn := (nestedPushforwardRestriction I.subschemeι hWV).hom.naturality
    (mapOn I hP hQ a U V hV)
  simp only [Functor.comp_map] at hn
  simp only [Category.assoc]
  rw [← reassoc_of% hn, ← comparisonOn_nested I Q hQ U V W hV hWV]
  rw [mapOn_pushforward, mapOn_pushforward]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id, Category.comp_id]
  have ht := (nestedRestriction hWV).hom.naturality a
  simp only [Functor.comp_map] at ht
  rw [Functor.map_comp, Category.assoc, ht]
  rw [← Category.assoc, comparisonOn_nested]
  simp only [Category.assoc]

end FLT.Mazur.FCurve.CoherentDevissage.ClosedDescentCharts
