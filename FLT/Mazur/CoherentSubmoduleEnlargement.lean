/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineCoherentSubmoduleRestriction
public import FLT.Mazur.CoherentClosedPushforward

/-!
# The affine chart step of coherent submodule enlargement

Transport of the affine extension theorem preserves the actual inclusion. In
particular a coherent submodule on an arbitrary open of a Noetherian affine
scheme extends to the affine scheme, with equality of restricted subobjects.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Scheme.Modules
open FLT.Mazur.FCurve.CoherentDevissage

universe u

namespace FLT.Mazur.CoherentSubmoduleEnlargement

variable {X Y : Scheme.{u}}

/-- Restriction along any open immersion preserves monomorphisms. -/
lemma restrictMap_mono (f : Y ⟶ X) [IsOpenImmersion f]
    {L M : X.Modules} (i : L ⟶ M) [Mono i] : Mono ((restrictFunctor f).map i) := by
  apply (SheafOfModules.forget Y.ringCatSheaf).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro V
  exact ModuleSubobjectCoverEquality.app_injective i (f ''ᵁ V.unop)

/-- The restriction unit for a scheme isomorphism is invertible. -/
lemma iso_unit_isIso (f : Y ⟶ X) [IsIso f] (M : X.Modules) :
    IsIso ((restrictAdjunction f).unit.app M) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro V
  rw [restrictAdjunction_unit_app_app]
  have he : f ''ᵁ (f ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Hom.opensRange_of_isIso, top_inf_eq]
  have hh : (homOfLE (f.image_preimage_le V)).op = (eqToHom he).op :=
    Subsingleton.elim _ _
  rw [hh]
  infer_instance

/-- Restricting to an inverse-image open commutes with open-immersion restriction. -/
def restrictionSquare (f : Y ⟶ X) [IsOpenImmersion f] (U : X.Opens) :
    restrictFunctor U.ι ⋙ restrictFunctor (f ∣_ U) ≅
      restrictFunctor f ⋙ restrictFunctor (f ⁻¹ᵁ U).ι :=
  (restrictFunctorComp (f ∣_ U) U.ι).symm ≪≫
    restrictFunctorCongr (morphismRestrict_ι f U) ≪≫
    restrictFunctorComp (f ⁻¹ᵁ U).ι f

/-- Restriction evaluates a morphism on image opens. -/
lemma restriction_app (f : Y ⟶ X) [IsOpenImmersion f] {L M : X.Modules}
    (i : L ⟶ M) (V : Y.Opens) :
    ((restrictFunctor f).map i).app V = i.app (f ''ᵁ V) := rfl

set_option maxHeartbeats 800000 in
-- The nested restriction functors require extra reduction of their module structures.
/-- The open base-change comparison intertwines the two restriction units. -/
lemma restrictionSquare_unit (f : Y ⟶ X) [IsOpenImmersion f] (U : X.Opens)
    (M : X.Modules) :
    (restrictFunctor U.ι).map ((restrictAdjunction f).unit.app M) ≫
        (closedPushforwardRestriction f U).hom.app (M.restrict f) =
      (restrictAdjunction (f ∣_ U)).unit.app (M.restrict U.ι) ≫
        (pushforward (f ∣_ U)).map ((restrictionSquare f U).hom.app M) := by
  apply Scheme.Modules.hom_ext
  intro V
  simp only [Hom.comp_app, restriction_app, pushforward_map_app,
    restrictAdjunction_unit_app_app, closedPushforwardRestriction_hom_app,
    restrictionSquare, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    restrictFunctorComp_inv_app_app, restrictFunctorComp_hom_app_app,
    restrictFunctorCongr_hom_app_app, restrict_map, ← CategoryTheory.Functor.map_comp]
  congr 1

/-- An extension records its inclusion and its comparison with the given subsheaf. -/
structure Extension (M : X.Modules) (U : X.Opens) (L : U.toScheme.Modules)
    (i : L ⟶ M.restrict U.ι) where
  /-- The constructed module on the larger scheme. -/
  obj : X.Modules
  /-- Its inclusion in the original ambient module. -/
  inclusion : obj ⟶ M
  /-- The inclusion is a monomorphism. -/
  inclusion_mono : Mono inclusion
  /-- The constructed module is locally finitely presented. -/
  coherent : obj.IsFinitePresentation
  /-- Restriction recovers the given module. -/
  comparison : obj.restrict U.ι ≅ L
  /-- The comparison identifies the actual inclusions. -/
  commutes : comparison.hom ≫ i = (restrictFunctor U.ι).map inclusion

attribute [instance] Extension.inclusion_mono Extension.coherent

/-- The extension recovers the prescribed subobject, not just its underlying module. -/
theorem Extension.subobject_eq {M : X.Modules} {U : X.Opens}
    {L : U.toScheme.Modules} {i : L ⟶ M.restrict U.ι} [Mono i]
    (E : Extension M U L i) :
    Subobject.mk ((restrictFunctor U.ι).map E.inclusion) = Subobject.mk i :=
  Subobject.mk_eq_mk_of_comm _ _ E.comparison E.commutes

/-- Transport an extension through a scheme isomorphism and its open restriction square. -/
theorem extension_of_iso (f : Y ⟶ X) [IsIso f] (M : X.Modules) (U : X.Opens)
    (L : U.toScheme.Modules) (i : L ⟶ M.restrict U.ι)
    (E : Extension (M.restrict f) (f ⁻¹ᵁ U) (L.restrict (f ∣_ U))
      ((restrictFunctor (f ∣_ U)).map i ≫ (restrictionSquare f U).hom.app M)) :
    Nonempty (Extension M U L i) := by
  have huM := iso_unit_isIso f M
  have huL := iso_unit_isIso (f ∣_ U) L
  let N := (pushforward f).obj E.obj
  let b : N ⟶ M := (pushforward f).map E.inclusion ≫
    inv ((restrictAdjunction f).unit.app M)
  have hb : Mono b := by dsimp [b]; infer_instance
  have hN : N.IsFinitePresentation := coherentPresentation_pushforwardIso (asIso f) E.obj
  let e : N.restrict U.ι ≅ L :=
    (closedPushforwardRestriction f U).app E.obj ≪≫
      (pushforward (f ∣_ U)).mapIso E.comparison ≪≫
      (asIso ((restrictAdjunction (f ∣_ U)).unit.app L)).symm
  refine ⟨⟨N, b, hb, hN, e, ?_⟩⟩
  apply (cancel_mono ((restrictFunctor U.ι).map ((restrictAdjunction f).unit.app M))).mp
  apply (cancel_mono ((closedPushforwardRestriction f U).hom.app (M.restrict f))).mp
  have hn := (restrictAdjunction (f ∣_ U)).unit.naturality i
  have hB := (closedPushforwardRestriction f U).hom.naturality E.inclusion
  simp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.id_map] at hn hB
  dsimp only [e, b]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_inv,
    Functor.map_comp, Category.assoc]
  rw [← Category.assoc ((restrictFunctor U.ι).map (inv _)),
    ← Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [restrictionSquare_unit]
  rw [← Category.assoc i, hn]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, E.commutes]
  exact hB.symm

/-- A coherent subsheaf on any open of a Noetherian affine scheme extends coherently. -/
theorem exists_affine_extension [IsAffine X] [IsLocallyNoetherian X]
    (M : X.Modules) [M.IsFinitePresentation] (U : X.Opens)
    (L : U.toScheme.Modules) [L.IsFinitePresentation] (i : L ⟶ M.restrict U.ι) [Mono i] :
    Nonempty (Extension M U L i) := by
  have hR : IsNoetherianRing Γ(X, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  let f := X.isoSpec.inv
  let W := f ⁻¹ᵁ U
  let a : L.restrict (f ∣_ U) ⟶ (M.restrict f).restrict W.ι :=
    (restrictFunctor (f ∣_ U)).map i ≫ (restrictionSquare f U).hom.app M
  have hM := coherentPresentation_restrict f M
  have hL := coherentPresentation_restrict (f ∣_ U) L
  have hi := restrictMap_mono (f ∣_ U) i
  have ha : Mono a := by dsimp [a]; infer_instance
  obtain ⟨P, _, hP, _, e, he⟩ :=
    AffineCoherentSubmoduleRestriction.exists_coherent_extension W
      (NoetherianSpace.isCompact _) (L.restrict (f ∣_ U)) a
  exact extension_of_iso f M U L i
    ⟨tilde (ModuleCat.of Γ(X, ⊤) P),
      AffineCoherentSubmoduleRestriction.coefficientInclusion (M.restrict f) P,
      inferInstance, hP, e, he⟩

/-- The overlap with an arbitrary open supplies a constructed extension on an affine chart.
The comparison in the output identifies both inclusions on the entire overlap. -/
theorem exists_affine_overlap_extension [IsLocallyNoetherian X]
    (M : X.Modules) [M.IsFinitePresentation] (U V : X.Opens) (hV : IsAffineOpen V)
    (L : U.toScheme.Modules) [L.IsFinitePresentation] (i : L ⟶ M.restrict U.ι) [Mono i] :
    Nonempty (Extension (M.restrict V.ι) (V.ι ⁻¹ᵁ U) (L.restrict (V.ι ∣_ U))
      ((restrictFunctor (V.ι ∣_ U)).map i ≫ (restrictionSquare V.ι U).hom.app M)) := by
  have hA : IsAffine V.toScheme := hV
  have hN := isLocallyNoetherian_of_isOpenImmersion V.ι
  have hM := coherentPresentation_restrict V.ι M
  have hL := coherentPresentation_restrict (V.ι ∣_ U) L
  have hi := restrictMap_mono (V.ι ∣_ U) i
  exact exists_affine_extension (M.restrict V.ι) (V.ι ⁻¹ᵁ U)
    (L.restrict (V.ι ∣_ U)) _

end FLT.Mazur.CoherentSubmoduleEnlargement
