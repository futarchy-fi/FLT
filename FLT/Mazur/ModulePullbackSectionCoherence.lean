/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModulePullbackRestrictionPasting

/-!
# Restriction comparisons on adjunction-unit sections

The pullback restriction isomorphism transports actual module sections through
its square of adjunctions, without a freeness or affineness assumption.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.ModulePullbackSectionCoherence
open FCurve
variable {X Y Z W : Scheme.{u}}

private lemma conj_inv {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (e : L₂ ≅ L₁) :
    conjugateEquiv a₂ a₁ e.inv = inv (conjugateEquiv a₁ a₂ e.hom) := by
  apply (cancel_epi (conjugateEquiv a₁ a₂ e.hom)).mp
  rw [conjugateEquiv_comp, e.inv_hom_id, conjugateEquiv_id, IsIso.hom_inv_id]

private lemma conj_comp_hom (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv (pullbackPushforwardAdjunction (f ≫ g))
      ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
      (pullbackComp f g).hom = (pushforwardComp f g).inv := by
  rw [← Iso.symm_inv (pullbackComp f g), conj_inv]
  simp only [Iso.symm_hom, conjugateEquiv_pullbackComp_inv]
  exact IsIso.inv_eq_of_hom_inv_id (Iso.hom_inv_id _)

private lemma conj_congr {f g : X ⟶ Y} (h : f = g) :
    conjugateEquiv (pullbackPushforwardAdjunction g) (pullbackPushforwardAdjunction f)
      (pullbackCongr h).hom = (pushforwardCongr h).inv := by
  subst g
  simp only [pullbackCongr, eqToIso_refl, Iso.refl_hom, conjugateEquiv_id]
  ext M U x
  simp

private lemma conj_restrict_inv (f : X ⟶ Y) [IsOpenImmersion f] :
    conjugateEquiv (restrictAdjunction f) (pullbackPushforwardAdjunction f)
      (restrictFunctorIsoPullback f).inv = 𝟙 _ := by
  rw [conj_inv]
  simp only [conjugateEquiv_restrictFunctorIsoPullback, IsIso.inv_id]

/-- The restriction comparison is the mate of the actual pushforward square. -/
lemma conjugate_restrict_square (f : X ⟶ Y) (g : Z ⟶ W) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] (h : i ≫ f = g ≫ j) :
    conjugateEquiv ((restrictAdjunction j).comp (pullbackPushforwardAdjunction g))
      ((pullbackPushforwardAdjunction f).comp (restrictAdjunction i))
        (modulePullbackRestrictNatIso f g i j h).hom =
      (pushforwardComp g j).hom ≫ (pushforwardCongr h).inv ≫
        (pushforwardComp i f).inv := by
  dsimp only [modulePullbackRestrictNatIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom]
  rw [← conjugateEquiv_comp _
    ((pullbackPushforwardAdjunction f).comp (pullbackPushforwardAdjunction i)) _]
  rw [← conjugateEquiv_comp _ (pullbackPushforwardAdjunction (i ≫ f)) _]
  rw [← conjugateEquiv_comp _ (pullbackPushforwardAdjunction (g ≫ j)) _]
  rw [← conjugateEquiv_comp _
    ((pullbackPushforwardAdjunction j).comp (pullbackPushforwardAdjunction g)) _]
  rw [conjugateEquiv_whiskerRight, conjugateEquiv_whiskerLeft, conj_restrict_inv,
    conjugateEquiv_restrictFunctorIsoPullback, conj_comp_hom, conj_congr,
    conjugateEquiv_pullbackComp_inv]
  simp

/-- The comparison intertwines the units of the two composite adjunctions. -/
lemma restrict_square_unit (f : X ⟶ Y) (g : Z ⟶ W) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] (h : i ≫ f = g ≫ j) (M : Y.Modules) :
    (((restrictAdjunction j).comp (pullbackPushforwardAdjunction g)).unit.app M) ≫
      ((pushforwardComp g j).hom ≫ (pushforwardCongr h).inv ≫
        (pushforwardComp i f).inv).app _ =
    (((pullbackPushforwardAdjunction f).comp (restrictAdjunction i)).unit.app M) ≫
      (pushforward i ⋙ pushforward f).map
        (modulePullbackRestrictIso f g i j h M).hom := by
  have e := unit_conjugateEquiv
    ((restrictAdjunction j).comp (pullbackPushforwardAdjunction g))
    ((pullbackPushforwardAdjunction f).comp (restrictAdjunction i))
    (modulePullbackRestrictNatIso f g i j h).hom M
  rw [conjugate_restrict_square] at e
  exact e

/-- On an inverse-image open, the comparison carries the ambient unit to the chart unit. -/
lemma open_unit (f : X ⟶ Y) (U : Y.Opens) (M : Y.Modules)
    (V : Y.Opens) (m : Γ(M, V)) :
    (modulePullbackOpenIso f U M).hom.app ((f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ V))
      (((restrictAdjunction (f ⁻¹ᵁ U).ι).unit.app ((pullback f).obj M)).app (f ⁻¹ᵁ V)
        (((pullbackPushforwardAdjunction f).unit.app M).app V m)) =
    (((pushforwardComp (f ∣_ U) U.ι).hom ≫
      (pushforwardCongr (morphismRestrict_ι f U).symm).inv ≫
      (pushforwardComp (f ⁻¹ᵁ U).ι f).inv).app
        ((pullback (f ∣_ U)).obj (M.restrict U.ι))).app V
      (((pullbackPushforwardAdjunction (f ∣_ U)).unit.app (M.restrict U.ι)).app
        (U.ι ⁻¹ᵁ V) (((restrictAdjunction U.ι).unit.app M).app V m)) := by
  exact (congrArg (fun k ↦ k.app V m)
    (restrict_square_unit f (f ∣_ U) (f ⁻¹ᵁ U).ι U.ι
      (morphismRestrict_ι f U).symm M)).symm

/-- Ambient sections identify with sections of the open restriction. -/
def chartSection (M : Y.Modules) (U : Y.Opens) (m : Γ(M, U)) :
    Γ(M.restrict U.ι, ⊤) :=
  M.presheaf.map (eqToHom U.ι_image_top).op m

set_option maxHeartbeats 800000 in
-- Transporting the two composite units unfolds the chosen pullback adjunctions.
/-- The pullback open comparison agrees with the unit on every chart section. -/
lemma open_unit_top (f : X ⟶ Y) (U : Y.Opens) (M : Y.Modules) (m : Γ(M, U)) :
    (modulePullbackOpenIso f U M).hom.app ⊤
      (chartSection ((pullback f).obj M) (f ⁻¹ᵁ U)
        (((pullbackPushforwardAdjunction f).unit.app M).app U m)) =
    ((pullbackPushforwardAdjunction (f ∣_ U)).unit.app (M.restrict U.ι)).app ⊤
      (chartSection M U m) := by
  have e := open_unit f U M U m
  simp only [NatTrans.comp_app, Hom.comp_app, ConcreteCategory.comp_apply,
    pushforwardComp_hom_app_app, pushforwardCongr_inv_app_app,
    pushforwardComp_inv_app_app, restrictAdjunction_unit_app_app] at e
  have et := congrArg
    (((pullback (f ∣_ U)).obj (M.restrict U.ι)).presheaf.map
      (eqToHom (Scheme.Opens.ι_preimage_self (f ⁻¹ᵁ U)).symm).op) e
  erw [← ConcreteCategory.comp_apply,
    ← (modulePullbackOpenIso f U M).hom.mapPresheaf.naturality] at et
  simp only [ConcreteCategory.comp_apply] at et
  erw [ConcreteCategory.id_apply, ConcreteCategory.id_apply] at et
  erw [restrict_map, ← Functor.map_comp_apply, ← Functor.map_comp_apply] at et
  have hn := (((pullbackPushforwardAdjunction (f ∣_ U)).unit.app
    (M.restrict U.ι)).mapPresheaf.naturality
      (eqToHom U.ι_preimage_self.symm).op)
  have hn' := congrArg (fun k ↦ k
    (M.presheaf.map (homOfLE (U.ι.image_preimage_le U)).op m)) hn
  simp only [ConcreteCategory.comp_apply, mapPresheaf_app] at hn'
  erw [pushforward_obj_presheaf_map (f ∣_ U)
    (M := (pullback (f ∣_ U)).obj (M.restrict U.ι)),
    restrict_map M U.ι, ← Functor.map_comp_apply] at hn'
  exact et.trans hn'.symm

end FLT.Mazur.ModulePullbackSectionCoherence
