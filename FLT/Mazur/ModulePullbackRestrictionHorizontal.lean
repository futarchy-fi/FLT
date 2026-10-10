/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModulePullbackSectionCoherence

/-!
# Horizontal composition of actual restriction-pullback comparisons

Two consecutive geometric base changes retain the original restriction comparison.
The proof uses the actual pushforward mates, including all equality transports.
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
variable (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (f' : Y₀ ⟶ Y₁) (g' : Y₁ ⟶ Y₂)
variable (i : Y₀ ⟶ X₀) (j : Y₁ ⟶ X₁) (k : Y₂ ⟶ X₂)
variable [IsOpenImmersion i] [IsOpenImmersion j] [IsOpenImmersion k]
variable (hf : i ≫ f = f' ≫ j) (hg : j ≫ g = g' ≫ k)

private lemma horizontal :
    Functor.whiskerRight (pullbackComp f g).hom (restrictFunctor i) ≫
        (modulePullbackRestrictNatIso (f ≫ g) (f' ≫ g') i k
          (by rw [← Category.assoc, hf, Category.assoc, hg, Category.assoc])).hom =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (pullback g) (modulePullbackRestrictNatIso f f' i j hf).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (modulePullbackRestrictNatIso g g' j k hg).hom (pullback f') ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (restrictFunctor k) (pullbackComp f' g').hom := by
  apply (conjugateEquiv
    ((restrictAdjunction k).comp (pullbackPushforwardAdjunction (f' ≫ g')))
    (((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f)).comp
      (restrictAdjunction i))).injective
  rw [← conjugateEquiv_comp _
    ((pullbackPushforwardAdjunction (f ≫ g)).comp (restrictAdjunction i)) _]
  rw [conjugateEquiv_whiskerRight, conj_comp_hom,
    ModulePullbackSectionCoherence.conjugate_restrict_square]
  rw [← conjugateEquiv_comp _ ((pullbackPushforwardAdjunction g).comp
    ((pullbackPushforwardAdjunction f).comp (restrictAdjunction i))) _]
  rw [← conjugateEquiv_comp _ ((pullbackPushforwardAdjunction g).comp
    ((restrictAdjunction j).comp (pullbackPushforwardAdjunction f'))) _]
  rw [← conjugateEquiv_comp _ (((pullbackPushforwardAdjunction g).comp
    (restrictAdjunction j)).comp (pullbackPushforwardAdjunction f')) _]
  rw [← conjugateEquiv_comp _ (((restrictAdjunction k).comp
    (pullbackPushforwardAdjunction g')).comp (pullbackPushforwardAdjunction f')) _]
  rw [← conjugateEquiv_comp _ ((restrictAdjunction k).comp
    ((pullbackPushforwardAdjunction g').comp (pullbackPushforwardAdjunction f'))) _]
  rw [conjugateEquiv_whiskerRight, conjugateEquiv_whiskerLeft,
    conjugateEquiv_whiskerLeft, conj_comp_hom,
    ModulePullbackSectionCoherence.conjugate_restrict_square,
    ModulePullbackSectionCoherence.conjugate_restrict_square,
    conj_assoc_inv, conjugateEquiv_associator_hom, conjugateEquiv_associator_hom]
  ext M U x
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.associator_hom_app,
    Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, pushforward_map_app,
    pushforwardComp_hom_app_app, pushforwardComp_inv_app_app,
    pushforwardCongr_inv_app_app, Scheme.Modules.Hom.id_app]
  change M.presheaf.map _ x = M.presheaf.map _ (M.presheaf.map _ x)
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Original restriction comparisons commute with two successive geometric pullbacks. -/
lemma modulePullbackRestrictIso_horizontal (M : X₂.Modules) :
    (restrictFunctor i).mapIso ((pullbackComp f g).app M) ≪≫
        modulePullbackRestrictIso (f ≫ g) (f' ≫ g') i k
          (by rw [← Category.assoc, hf, Category.assoc, hg, Category.assoc]) M =
      modulePullbackRestrictIso f f' i j hf ((pullback g).obj M) ≪≫
        (pullback f').mapIso (modulePullbackRestrictIso g g' j k hg M) ≪≫
        (pullbackComp f' g').app (M.restrict k) := by
  apply Iso.ext
  simpa [modulePullbackRestrictNatIso, modulePullbackRestrictIso] using
    congrArg (fun t ↦ t.app M) (horizontal f g f' g' i j k hf hg)

end FLT.Mazur.FCurve
