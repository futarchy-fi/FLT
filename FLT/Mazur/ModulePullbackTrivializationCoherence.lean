/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModulePullbackRestrictionPasting
public import FLT.Mazur.ModuleSheafTensorRestrict
public import FLT.Mazur.ModuleSheafUnitCocycleRestrict

/-!
# Restriction coherence for pulled-back trivializations

The chosen trivialization commutes with open restriction. For a sheaf descended
from units, its pulled-back trivializations have the pulled-back transition
coefficients on every common subopen.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

open Scheme.Modules

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

variable {X₀ X₁ X₂ Y₀ Y₁ Y₂ : Scheme.{u}}

private lemma restrictFunctorCongr_refl (X Y : Scheme.{u}) (i : X ⟶ Y) [IsOpenImmersion i] :
    restrictFunctorCongr (rfl : i = i) = Iso.refl _ := by
  apply Iso.ext
  ext M U x
  simp
  rfl

/-- The comparison respects equality transports of the open immersions. -/
lemma modulePullbackRestrictIso_congr
    (f : X₀ ⟶ Y₀) (g : X₁ ⟶ Y₁)
    (i i' : X₁ ⟶ X₀) (j j' : Y₁ ⟶ Y₀)
    [IsOpenImmersion i] [IsOpenImmersion i']
    [IsOpenImmersion j] [IsOpenImmersion j']
    (hi : i = i') (hj : j = j') (h : i ≫ f = g ≫ j) (h' : i' ≫ f = g ≫ j')
    (M : Y₀.Modules) :
    (restrictFunctorCongr hi).app ((pullback f).obj M) ≪≫
      modulePullbackRestrictIso f g i' j' h' M =
    modulePullbackRestrictIso f g i j h M ≪≫
      (pullback g).mapIso ((restrictFunctorCongr hj).app M) := by
  subst i'; subst j'
  apply Iso.ext
  simp [restrictFunctorCongr_refl]

private lemma trivialization_pasting
    (f₀ : X₀ ⟶ Y₀) (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (i₁ : X₁ ⟶ X₀) (i₂ : X₂ ⟶ X₁) (j₁ : Y₁ ⟶ Y₀) (j₂ : Y₂ ⟶ Y₁)
    [IsOpenImmersion i₁] [IsOpenImmersion i₂]
    [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (h₁ : i₁ ≫ f₀ = f₁ ≫ j₁) (h₂ : i₂ ≫ f₁ = f₂ ≫ j₂)
    (M : Y₀.Modules) (e : M.restrict j₁ ≅ structureModule Y₁) :
    (modulePullbackRestrictIso f₀ f₂ (i₂ ≫ i₁) (j₂ ≫ j₁)
      (by rw [Category.assoc, h₁, ← Category.assoc, h₂, Category.assoc]) M).hom ≫
      (pullback f₂).map ((restrictFunctorComp j₂ j₁).hom.app M ≫
        (restrictFunctor j₂).map e.hom ≫ (restrictUnitIso j₂).hom) ≫
      (modulePullbackUnitIso f₂).hom =
    (restrictFunctorComp i₂ i₁).hom.app ((pullback f₀).obj M) ≫
      (restrictFunctor i₂).map ((modulePullbackRestrictIso f₀ f₁ i₁ j₁ h₁ M).hom ≫
        (pullback f₁).map e.hom ≫ (modulePullbackUnitIso f₁).hom) ≫
      (restrictUnitIso i₂).hom := by
  rw [modulePullbackRestrictIso_pasting f₀ f₁ f₂ i₁ i₂ j₁ j₂ h₁ h₂ M]
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc]
  simp only [Functor.map_comp, Category.assoc]
  rw [← modulePullbackRestrictIso_naturality_assoc f₁ f₂ i₂ j₂ h₂ e.hom]
  rw [modulePullbackRestrictIso_unit]

/-- Pulling back a trivialization commutes with restricting its source chart. -/
lemma modulePullbackTrivialization_restrict {X Y : Scheme.{u}}
    (f : X ⟶ Y) {M : Y.Modules} {V U : Y.Opens} (h : V ≤ U)
    (e : M.restrict U.ι ≅ structureModule U.toScheme) :
    ModuleSheafTensor.restrictTrivialization ((Opens.map f.base).map (homOfLE h)).le
      (modulePullbackTrivialization f e) =
    modulePullbackTrivialization f (ModuleSheafTensor.restrictTrivialization h e) := by
  let hX := ((Opens.map f.base).map (homOfLE h)).le
  have h₁ := (morphismRestrict_ι f U).symm
  have h₂ : X.homOfLE hX ≫ f ∣_ U = f ∣_ V ≫ Y.homOfLE h :=
    (morphismRestrict_homOfLE f V U h).symm
  have ht : (X.homOfLE hX ≫ (f ⁻¹ᵁ U).ι) ≫ f =
      f ∣_ V ≫ (Y.homOfLE h ≫ U.ι) := by
    rw [Category.assoc, h₁, ← Category.assoc, h₂, Category.assoc]
  have hp := trivialization_pasting f (f ∣_ U) (f ∣_ V)
    (f ⁻¹ᵁ U).ι (X.homOfLE hX) U.ι (Y.homOfLE h) h₁ h₂ M e
  have hc := congrArg Iso.hom (modulePullbackRestrictIso_congr f (f ∣_ V)
    (f ⁻¹ᵁ V).ι (X.homOfLE hX ≫ (f ⁻¹ᵁ U).ι)
    V.ι (Y.homOfLE h ≫ U.ι) (X.homOfLE_ι hX).symm (Y.homOfLE_ι h).symm
    (morphismRestrict_ι f V).symm ht M)
  apply Iso.ext
  simp only [ModuleSheafTensor.restrictTrivialization, modulePullbackTrivialization,
    modulePullbackOpenIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom] at hc ⊢
  rw [← hp]
  rw [← Category.assoc, hc]
  simp only [Functor.map_comp, Category.assoc]

namespace ModuleSheafUnitCocycle.Cocycle

variable {X Y : Scheme.{u}} {ι : Type u} {U : ι → Y.Opens} (g : Cocycle U)

/-- Restricting a cocycle chart agrees with direct component evaluation. -/
lemma restrictTrivialization_onOpenIso (i : ι) {A B : Y.Opens} (h : A ≤ B) (hi : B ≤ U i) :
    ModuleSheafTensor.restrictTrivialization h (g.onOpenIso i B hi) =
      g.onOpenIso i A (h.trans hi) := by
  apply Iso.ext
  apply Scheme.Modules.hom_ext
  intro W
  ext s
  simp only [ModuleSheafTensor.restrictTrivialization, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    restrictFunctorCongr_hom_app_app, restrictFunctorComp_hom_app_app]
  change ((Y.homOfLE h).appIso W).hom
    (g.evaluate i ((B.ι_image_le ((Y.homOfLE h) ''ᵁ W)).trans hi)
      _) =
      g.evaluate i ((A.ι_image_le W).trans (h.trans hi)) s
  apply (ConcreteCategory.bijective_of_isIso ((Y.homOfLE h).appIso W).inv).1
  rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply,
    Scheme.Hom.appIso_homOfLE_inv]
  change res _ (res _ (res _ (s.1 i))) = res _ (res _ (s.1 i))
  simp only [res_res]

/-- The pulled-back component charts change by the pulled-back transition unit. -/
lemma pullback_onOpenIso_change (f : X ⟶ Y) (i j : ι) (V : Y.Opens)
    (hi : V ≤ U i) (hj : V ≤ U j) (A : V.toScheme.Opens)
    (W : (f ⁻¹ᵁ V).toScheme.Opens) (hW : W ≤ (f ∣_ V) ⁻¹ᵁ A)
    (r : Γ((f ⁻¹ᵁ V).toScheme, W)) :
    ((modulePullbackTrivialization f (g.onOpenIso j V hj)).inv ≫
      (modulePullbackTrivialization f (g.onOpenIso i V hi)).hom).app W r =
    (f ∣_ V).appLE A W hW
      (g.unit i j (V.ι ''ᵁ A) ((V.ι_image_le A).trans hi)
        ((V.ι_image_le A).trans hj) : Γ(Y, V.ι ''ᵁ A)) * r := by
  rw [modulePullbackTrivialization_change f _ _ A W hW,
    g.onOpenIso_change, mul_one]
set_option maxRecDepth 2048 in
-- Comparing module structures traverses two nested chart restrictions.
/-- The chosen pulled-back trivializations obey the transition law on every common subopen. -/
lemma pullback_restrictIso_change (f : X ⟶ Y) (i j : ι) (V : Y.Opens)
    (hi : V ≤ U i) (hj : V ≤ U j) (A : V.toScheme.Opens)
    (W : (f ⁻¹ᵁ V).toScheme.Opens) (hW : W ≤ (f ∣_ V) ⁻¹ᵁ A)
    (r : Γ((f ⁻¹ᵁ V).toScheme, W)) :
    ((ModuleSheafTensor.restrictTrivialization (f.preimage_mono hj)
        (modulePullbackTrivialization f (g.restrictIso j))).inv ≫
      (ModuleSheafTensor.restrictTrivialization (f.preimage_mono hi)
        (modulePullbackTrivialization f (g.restrictIso i))).hom).app W r =
    (f ∣_ V).appLE A W hW
      (g.unit i j (V.ι ''ᵁ A) ((V.ι_image_le A).trans hi)
        ((V.ι_image_le A).trans hj) : Γ(Y, V.ι ''ᵁ A)) * r := by
  rw [modulePullbackTrivialization_restrict f hj (g.restrictIso j),
    modulePullbackTrivialization_restrict f hi (g.restrictIso i)]
  simp only [restrictIso]
  rw [g.restrictTrivialization_onOpenIso j hj le_rfl,
    g.restrictTrivialization_onOpenIso i hi le_rfl]
  exact g.pullback_onOpenIso_change f i j V hi hj A W hW r

end ModuleSheafUnitCocycle.Cocycle

end FLT.Mazur.FCurve
