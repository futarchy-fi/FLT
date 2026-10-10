/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafOverlapImageTransition

/-!
# Sections of an open immersion pullback

The restriction/pullback comparison sends sections on the image to actual
pullback sections. Its counit recovers the original chart section.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.ModuleSheafOpenImmersionSections

variable {X Y : Scheme.{u}} (i : Y ⟶ X) [IsOpenImmersion i]

/-- Pullback sections on an open chart are its ambient image sections. -/
def imageSectionsIso (M : X.Modules) (U : Y.Opens) :
    Γ(M, i ''ᵁ U) ≅ Γ((pullback i).obj M, U) :=
  (M.restrictAppIso i U).symm ≪≫
    asIso (((restrictFunctorIsoPullback i).hom.app M).app U)

/-- The chart section comparison commutes with ambient module morphisms. -/
lemma imageSectionsIso_naturality {M N : X.Modules} (a : M ⟶ N) (U : Y.Opens) :
    a.app (i ''ᵁ U) ≫ (imageSectionsIso i N U).hom =
      (imageSectionsIso i M U).hom ≫ ((pullback i).map a).app U := by
  exact congrArg (fun k ↦ k.app U) ((restrictFunctorIsoPullback i).hom.naturality a)

/-- The open-immersion counit is the actual pullback adjunction counit. -/
lemma openCounitIso_hom (M : Y.Modules) :
    (ModuleSheafOverlapImageTransition.openCounitIso i M).hom =
      (pullbackPushforwardAdjunction i).counit.app M := by
  apply (cancel_epi ((restrictFunctorIsoPullback i).hom.app ((pushforward i).obj M))).mp
  change _ ≫ ((restrictFunctorIsoPullback i).inv.app _ ≫ _) = _
  rw [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  exact (Adjunction.leftAdjointUniq_hom_app_counit
    (restrictAdjunction i) (pullbackPushforwardAdjunction i) M).symm

/-- The counit evaluates an image section by the canonical preimage equality. -/
lemma imageSectionsIso_counit (M : Y.Modules) (U : Y.Opens) :
    (imageSectionsIso i ((pushforward i).obj M) U).hom ≫
        (ModuleSheafOverlapImageTransition.openCounitIso i M).hom.app U =
      M.presheaf.map (eqToHom (i.preimage_image_eq U).symm).op := by
  rw [openCounitIso_hom]
  exact congrArg (fun k ↦ k.app U) (Adjunction.leftAdjointUniq_hom_app_counit
    (restrictAdjunction i) (pullbackPushforwardAdjunction i) M)

/-- The section comparison is normalized by the actual pullback unit. -/
lemma imageSectionsIso_unit (M : X.Modules) (V : X.Opens) :
    M.presheaf.map (homOfLE (i.image_preimage_le V)).op ≫
        (imageSectionsIso i M (i ⁻¹ᵁ V)).hom =
      ((pullbackPushforwardAdjunction i).unit.app M).app V := by
  exact congrArg (fun k ↦ k.app V) (Adjunction.unit_leftAdjointUniq_hom_app
    (restrictAdjunction i) (pullbackPushforwardAdjunction i) M)

/-- The image section comparison commutes with restriction inside a chart. -/
lemma imageSectionsIso_restrict (M : X.Modules) {U V : Y.Opens} (h : U ⟶ V) :
    M.presheaf.map (i.opensFunctor.map h).op ≫ (imageSectionsIso i M U).hom =
      (imageSectionsIso i M V).hom ≫ ((pullback i).obj M).presheaf.map h.op := by
  exact (((restrictFunctorIsoPullback i).hom.app M).mapPresheaf.naturality h.op)

end FLT.Mazur.ModuleSheafOpenImmersionSections
