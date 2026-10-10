/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFreeSectionLineTransport

/-!
# Actual free-sheaf inclusions of transported section lines

An affine free-sheaf isomorphism recovers coordinates on ordinary vectors.
The induced isomorphism of actual line sheaves preserves their inclusions
into the original free sheaves, through the original sheaf isomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.AffineFreeSheafCoordinates
open AffineModuleGlobalSections NormalizedSectionLine FiniteFreeContragredient
variable (S : Scheme.{u}) [IsAffine S]

/-- Ordinary finite coordinate vectors give the actual free sheaf on the affine scheme. -/
def vectorFreeIso (ι : Type u) [Finite ι] :
    (affineTilde S).obj (ModuleCat.of Γ(S, ⊤) (ι → Γ(S, ⊤))) ≅ SheafOfModules.free ι :=
  (affineTilde S).mapIso (Finsupp.linearEquivFunOnFinite Γ(S, ⊤) Γ(S, ⊤) ι).symm.toModuleIso ≪≫
    freeIso S ι

variable {ι κ : Type u} [Finite ι] [Finite κ]

/-- The vector-coordinate isomorphism reconstructs the original free-sheaf isomorphism. -/
lemma vectorCoordinates_reconstruct
    (e : (SheafOfModules.free ι : S.Modules) ≅ SheafOfModules.free κ) :
    (affineTilde S).mapIso (functionCoordinates (coordinates S e)).toModuleIso =
      vectorFreeIso S ι ≪≫ e ≪≫ (vectorFreeIso S κ).symm := by
  change (affineTilde S).mapIso
    ((Finsupp.linearEquivFunOnFinite Γ(S, ⊤) Γ(S, ⊤) ι).symm.toModuleIso ≪≫
      coordinatesIso S e ≪≫
        (Finsupp.linearEquivFunOnFinite Γ(S, ⊤) Γ(S, ⊤) κ).toModuleIso) = _
  rw [Functor.mapIso_trans, Functor.mapIso_trans, coordinatesIso_reconstruct]
  simp only [vectorFreeIso, Iso.trans_symm, ← Functor.mapIso_symm, Iso.trans_assoc]
  rfl

/-- The actual affine line sheaf associated to its original coordinate submodule. -/
abbrev sectionLineSheaf (i : ι) (L : Chart Γ(S, ⊤) ι i) : S.Modules :=
  (affineTilde S).obj (ModuleCat.of Γ(S, ⊤) L.val)

/-- Inclusion of the actual line into the original free sheaf. -/
def sectionLineInclusion (i : ι) (L : Chart Γ(S, ⊤) ι i) :
    sectionLineSheaf S i L ⟶ SheafOfModules.free ι :=
  (affineTilde S).map (ModuleCat.ofHom L.val.subtype) ≫ (vectorFreeIso S ι).hom

instance (i : ι) (L : Chart Γ(S, ⊤) ι i) :
    IsSplitMono (sectionLineInclusion S i L) := by
  refine IsSplitMono.mk' ⟨(vectorFreeIso S ι).inv ≫
    (affineTilde S).map (ModuleCat.ofHom (retraction i L)), ?_⟩
  simp only [sectionLineInclusion, Category.assoc, Iso.hom_inv_id_assoc,
    ← Functor.map_comp]
  have h : ModuleCat.ofHom L.val.subtype ≫ ModuleCat.ofHom (retraction i L) =
      𝟙 (ModuleCat.of Γ(S, ⊤) L.val) := ModuleCat.hom_ext (retraction_subtype i L)
  rw [h]
  exact (affineTilde S).map_id _

/-- The original free-sheaf isomorphism transports the actual section line. -/
def sectionLineTransport
    (e : (SheafOfModules.free ι : S.Modules) ≅ SheafOfModules.free κ)
    (i : ι) (j : κ) (L : Chart Γ(S, ⊤) ι i) (a : Γ(S, ⊤)ˣ)
    (ha : functionCoordinates (coordinates S e) (generator Γ(S, ⊤) ι i L) j = a) :
    sectionLineSheaf S i L ≅
      sectionLineSheaf S j (linearTransport (functionCoordinates (coordinates S e)) i j L a ha) :=
  (affineTilde S).mapIso
    ((functionCoordinates (coordinates S e)).submoduleMap L.val).toModuleIso

attribute [local irreducible] affineTilde vectorFreeIso coordinates

/-- Transport preserves the inclusion through the genuine original free-sheaf map. -/
lemma sectionLineTransport_inclusion
    (e : (SheafOfModules.free ι : S.Modules) ≅ SheafOfModules.free κ)
    (i : ι) (j : κ) (L : Chart Γ(S, ⊤) ι i) (a : Γ(S, ⊤)ˣ)
    (ha : functionCoordinates (coordinates S e) (generator Γ(S, ⊤) ι i L) j = a) :
    (sectionLineTransport S e i j L a ha).hom ≫
        sectionLineInclusion S j
          (linearTransport (functionCoordinates (coordinates S e)) i j L a ha) =
      sectionLineInclusion S i L ≫ e.hom := by
  have h := congrArg Iso.hom (vectorCoordinates_reconstruct S e)
  dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    LinearEquiv.toModuleIso_hom] at h
  have hv : (affineTilde S).map
      (ModuleCat.ofHom (functionCoordinates (coordinates S e)).toLinearMap) ≫
      (vectorFreeIso S κ).hom = (vectorFreeIso S ι).hom ≫ e.hom := by
    rw [h]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  dsimp only [sectionLineTransport, sectionLineInclusion, Functor.mapIso_hom]
  rw [← Category.assoc, ← Functor.map_comp]
  have hm :
      ((functionCoordinates (coordinates S e)).submoduleMap L.val).toModuleIso.hom ≫
        ModuleCat.ofHom (linearTransport
          (functionCoordinates (coordinates S e)) i j L a ha).val.subtype =
      ModuleCat.ofHom L.val.subtype ≫
        ModuleCat.ofHom (functionCoordinates (coordinates S e)).toLinearMap := rfl
  rw [hm, Functor.map_comp, Category.assoc, hv, ← Category.assoc]

end FLT.Mazur.AffineFreeSheafCoordinates
