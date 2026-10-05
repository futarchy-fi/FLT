/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSourceSectionBaseChange

/-!
# Affine source charts of a pullback

Restricting a pullback to an open immersion is the pullback along the
composite. The comparison is chosen by adjunction, so it preserves the
original unit sections. On affine charts it gives the tensor description.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
open scoped ChangeOfRings

universe u

namespace FLT.Mazur.AffineSourcePullbackSections

open AffineModuleGlobalSections

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ X) [IsOpenImmersion i]

/-- The composite pullback has the iterated pushforward as right adjoint. -/
def compositeAdjunction : pullback (i ≫ f) ⊣ pushforward i ⋙ pushforward f :=
  (pullbackPushforwardAdjunction (i ≫ f)).ofNatIsoRight (pushforwardComp i f).symm

/-- The source restriction comparison, determined by the common right adjoint. -/
def restrictionIso : pullback f ⋙ restrictFunctor i ≅ pullback (i ≫ f) :=
  ((pullbackPushforwardAdjunction f).comp (restrictAdjunction i)).leftAdjointUniq
    (compositeAdjunction f i)

/-- The restriction comparison preserves the actual iterated unit sections. -/
lemma restrictionIso_unit (M : Y.Modules) (V : Y.Opens) (m : Γ(M, V)) :
    ((restrictionIso f i).hom.app M).app (i ⁻¹ᵁ (f ⁻¹ᵁ V))
      (((restrictAdjunction i).unit.app ((pullback f).obj M)).app (f ⁻¹ᵁ V)
        (((pullbackPushforwardAdjunction f).unit.app M).app V m)) =
    ((pullbackPushforwardAdjunction (i ≫ f)).unit.app M).app V m := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((pullbackPushforwardAdjunction f).comp (restrictAdjunction i))
    (compositeAdjunction f i) M
  have hu : (compositeAdjunction f i).unit.app M =
      (pullbackPushforwardAdjunction (i ≫ f)).unit.app M ≫
        (pushforwardComp i f).inv.app _ := by
    rw [← Adjunction.homEquiv_id (compositeAdjunction f i)]
    rw [compositeAdjunction, Adjunction.homEquiv_ofNatIsoRight_apply,
      Adjunction.homEquiv_id]
    rfl
  rw [hu] at h
  have h' := congrArg (fun k ↦ k.app V m) h
  simp only [Adjunction.comp_unit_app, Hom.comp_app, ConcreteCategory.comp_apply,
    Functor.comp_map, pushforward_map_app, pushforwardComp_inv_app_app] at h'
  exact h'

variable [IsAffine Z] [IsAffine Y] (M : Y.Modules) [M.IsQuasicoherent]

/-- Actual global sections of an affine source restriction are scalar extension. -/
def sectionsIso :
    (ModuleCat.extendScalars (i ≫ f).appTop.hom).obj ((sections Y).obj M) ≅
      (sections Z).obj (((pullback f).obj M).restrict i) :=
  AffineQuasiCoherentBaseChange.sectionsIso (i ≫ f) M ≪≫
    (sections Z).mapIso ((restrictionIso f i).app M).symm

omit [IsAffine Z] [IsAffine Y] [M.IsQuasicoherent] in
/-- On a source open, the comparison carries the restricted unit to the chart unit. -/
lemma restrictionIso_unit_top (U : X.Opens) (m : Γ(M, ⊤)) :
    ((restrictionIso f U.ι).hom.app M).app ⊤
      (((pullback f).obj M).presheaf.map (eqToHom U.ι_image_top).op
        (ModuleSourceSectionBaseChange.unitMap f M U m)) =
    ((pullbackPushforwardAdjunction (U.ι ≫ f)).unit.app M).app ⊤ m := by
  have h := restrictionIso_unit f U.ι M ⊤ m
  simp only [Scheme.Hom.preimage_top, restrictAdjunction_unit_app_app] at h
  convert h using 1
  change ((restrictionIso f U.ι).hom.app M).app ⊤
    (((pullback f).obj M).presheaf.map _
      (((pullback f).obj M).presheaf.map _ _)) = _
  rw [← Functor.map_comp_apply]
  rfl

omit [IsAffine Z] in
/-- On an affine source open the tensor isomorphism retains the original unit section. -/
lemma sectionsIso_open_tmul (U : X.affineOpens) (r : Γ(U.1, ⊤)) (m : Γ(M, ⊤)) :
    (sectionsIso f U.1.ι M).hom (r ⊗ₜ[Γ(Y, ⊤),(U.1.ι ≫ f).appTop.hom] m) =
      r • (show Γ(((pullback f).obj M).restrict U.1.ι, ⊤) from
        ((pullback f).obj M).presheaf.map (eqToHom U.1.ι_image_top).op
          (ModuleSourceSectionBaseChange.unitMap f M U.1 m)) := by
  let e := (sections U.1.toScheme).mapIso ((restrictionIso f U.1.ι).app M)
  apply (ConcreteCategory.bijective_of_isIso e.hom).injective
  change e.hom (e.inv ((AffineQuasiCoherentBaseChange.sectionsIso (U.1.ι ≫ f) M).hom
    (r ⊗ₜ[Γ(Y, ⊤),(U.1.ι ≫ f).appTop.hom] m))) = _
  rw [← ConcreteCategory.comp_apply, e.inv_hom_id, ConcreteCategory.id_apply]
  rw [e.hom.hom.map_smul, AffineQuasiCoherentBaseChange.sectionsIso_tmul]
  congr 1
  exact (restrictionIso_unit_top f M U.1 m).symm

end FLT.Mazur.AffineSourcePullbackSections
