/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModulePullbackUnitCoherence

/-!
# Pasting restriction comparisons for module pullbacks

The chosen comparison for two commuting open-immersion squares agrees with
pasting their individual comparisons. Transposing to pushforwards reduces the
coherence, including equality transports, to composition of section restrictions.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

open Scheme.Modules

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

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

/-- The restriction comparison as a natural isomorphism in the module. -/
def modulePullbackRestrictNatIso (f : X ⟶ Y) (g : Z ⟶ W) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] (h : i ≫ f = g ≫ j) :
    pullback f ⋙ restrictFunctor i ≅ restrictFunctor j ⋙ pullback g :=
  Functor.isoWhiskerLeft _ (restrictFunctorIsoPullback i) ≪≫ pullbackComp i f ≪≫
    pullbackCongr h ≪≫ (pullbackComp g j).symm ≪≫
      Functor.isoWhiskerRight (restrictFunctorIsoPullback j).symm _

private lemma conj_square (f : X ⟶ Y) (g : Z ⟶ W) (i : Z ⟶ X) (j : W ⟶ Y)
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

private lemma conj_restrict_comp_inv (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    conjugateEquiv (restrictAdjunction (f ≫ g))
      ((restrictAdjunction g).comp (restrictAdjunction f))
      (restrictFunctorComp f g).inv = (pushforwardComp f g).inv := by
  rw [conj_inv]
  simp only [conjugateEquiv_restrictFunctorComp]
  exact IsIso.inv_eq_of_hom_inv_id (Iso.hom_inv_id _)

private lemma conj_assoc_inv {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B}
    {L₃ : C ⥤ D} {R₃ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃) :
    conjugateEquiv ((a₁.comp a₂).comp a₃) (a₁.comp (a₂.comp a₃))
      (Functor.associator L₁ L₂ L₃).inv = (Functor.associator R₃ R₂ R₁).inv := by
  rw [conj_inv]
  simp only [conjugateEquiv_associator_hom]
  exact IsIso.inv_eq_of_hom_inv_id (Iso.hom_inv_id _)

variable {X₀ X₁ X₂ Y₀ Y₁ Y₂ : Scheme.{u}}

private lemma square_pasting
    (f₀ : X₀ ⟶ Y₀) (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (i₁ : X₁ ⟶ X₀) (i₂ : X₂ ⟶ X₁) (j₁ : Y₁ ⟶ Y₀) (j₂ : Y₂ ⟶ Y₁)
    [IsOpenImmersion i₁] [IsOpenImmersion i₂]
    [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (h₁ : i₁ ≫ f₀ = f₁ ≫ j₁) (h₂ : i₂ ≫ f₁ = f₂ ≫ j₂) :
    (modulePullbackRestrictNatIso f₀ f₂ (i₂ ≫ i₁) (j₂ ≫ j₁)
      (by rw [Category.assoc, h₁, ← Category.assoc, h₂, Category.assoc])).hom =
    Functor.whiskerLeft (pullback f₀) (restrictFunctorComp i₂ i₁).hom ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (modulePullbackRestrictNatIso f₀ f₁ i₁ j₁ h₁).hom (restrictFunctor i₂) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (restrictFunctor j₁) (modulePullbackRestrictNatIso f₁ f₂ i₂ j₂ h₂).hom ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (restrictFunctorComp j₂ j₁).inv (pullback f₂) := by
  apply (conjugateEquiv
    ((restrictAdjunction (j₂ ≫ j₁)).comp (pullbackPushforwardAdjunction f₂))
    ((pullbackPushforwardAdjunction f₀).comp (restrictAdjunction (i₂ ≫ i₁)))).injective
  rw [conj_square]
  rw [← conjugateEquiv_comp _ ((pullbackPushforwardAdjunction f₀).comp
    ((restrictAdjunction i₁).comp (restrictAdjunction i₂))) _]
  rw [← conjugateEquiv_comp _ (((pullbackPushforwardAdjunction f₀).comp
    (restrictAdjunction i₁)).comp (restrictAdjunction i₂)) _]
  rw [← conjugateEquiv_comp _ (((restrictAdjunction j₁).comp
    (pullbackPushforwardAdjunction f₁)).comp (restrictAdjunction i₂)) _]
  rw [← conjugateEquiv_comp _ ((restrictAdjunction j₁).comp
    ((pullbackPushforwardAdjunction f₁).comp (restrictAdjunction i₂))) _]
  rw [← conjugateEquiv_comp _ ((restrictAdjunction j₁).comp
    ((restrictAdjunction j₂).comp (pullbackPushforwardAdjunction f₂))) _]
  rw [← conjugateEquiv_comp _ (((restrictAdjunction j₁).comp
    (restrictAdjunction j₂)).comp (pullbackPushforwardAdjunction f₂)) _]
  rw [conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight,
    conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight,
    conjugateEquiv_restrictFunctorComp, conj_restrict_comp_inv,
    conj_square, conj_square, conj_assoc_inv, conj_assoc_inv,
    conjugateEquiv_associator_hom]
  ext M U x
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.associator_hom_app,
    Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, pushforward_map_app,
    pushforwardComp_hom_app_app, pushforwardComp_inv_app_app,
    pushforwardCongr_inv_app_app,
    Scheme.Modules.Hom.id_app]
  change M.presheaf.map _ x = M.presheaf.map _ (M.presheaf.map _ x)
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Restriction comparisons paste for two arbitrary commuting open-immersion squares. -/
lemma modulePullbackRestrictIso_pasting
    (f₀ : X₀ ⟶ Y₀) (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (i₁ : X₁ ⟶ X₀) (i₂ : X₂ ⟶ X₁) (j₁ : Y₁ ⟶ Y₀) (j₂ : Y₂ ⟶ Y₁)
    [IsOpenImmersion i₁] [IsOpenImmersion i₂]
    [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (h₁ : i₁ ≫ f₀ = f₁ ≫ j₁) (h₂ : i₂ ≫ f₁ = f₂ ≫ j₂) (M : Y₀.Modules) :
  modulePullbackRestrictIso f₀ f₂ (i₂ ≫ i₁) (j₂ ≫ j₁)
      (by rw [Category.assoc, h₁, ← Category.assoc, h₂, Category.assoc]) M =
    (Scheme.Modules.restrictFunctorComp i₂ i₁).app
        ((Scheme.Modules.pullback f₀).obj M) ≪≫
      (Scheme.Modules.restrictFunctor i₂).mapIso
        (modulePullbackRestrictIso f₀ f₁ i₁ j₁ h₁ M) ≪≫
      modulePullbackRestrictIso f₁ f₂ i₂ j₂ h₂ (M.restrict j₁) ≪≫
      (Scheme.Modules.pullback f₂).mapIso
        ((Scheme.Modules.restrictFunctorComp j₂ j₁).app M).symm := by
  apply Iso.ext
  simpa [modulePullbackRestrictNatIso, modulePullbackRestrictIso] using
    congrArg (fun t ↦ t.app M) (square_pasting f₀ f₁ f₂ i₁ i₂ j₁ j₂ h₁ h₂)

/-- Restriction comparisons are natural in the original module sheaf. -/
@[reassoc]
lemma modulePullbackRestrictIso_naturality (f : X ⟶ Y) (g : Z ⟶ W)
    (i : Z ⟶ X) (j : W ⟶ Y) [IsOpenImmersion i] [IsOpenImmersion j]
    (h : i ≫ f = g ≫ j) {M N : Y.Modules} (a : M ⟶ N) :
    (restrictFunctor i).map ((pullback f).map a) ≫
      (modulePullbackRestrictIso f g i j h N).hom =
    (modulePullbackRestrictIso f g i j h M).hom ≫
      (pullback g).map ((restrictFunctor j).map a) :=
  (modulePullbackRestrictNatIso f g i j h).hom.naturality a

end FLT.Mazur.FCurve
