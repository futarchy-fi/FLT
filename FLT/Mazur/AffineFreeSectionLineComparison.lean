/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineFreeSectionLineTransport

/-!
# Comparing specified section lines across actual free-sheaf charts

Equality with the image submodule constructs a comparison to any specified
normalized target line. The original ambient sheaf map determines it uniquely.
These comparisons satisfy the cocycle for genuine composed sheaf transitions.
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
variable {ι κ ν : Type u} [Finite ι] [Finite κ] [Finite ν]

/-- The image of the actual submodule defines a comparison to a specified target line. -/
def sectionLineCompare
    (e : (SheafOfModules.free ι : S.Modules) ≅ SheafOfModules.free κ)
    (i : ι) (j : κ) (L : Chart Γ(S, ⊤) ι i) (N : Chart Γ(S, ⊤) κ j)
    (h : L.val.map (functionCoordinates (coordinates S e)).toLinearMap = N.val) :
    sectionLineSheaf S i L ≅ sectionLineSheaf S j N :=
  (affineTilde S).mapIso
    (((functionCoordinates (coordinates S e)).submoduleMap L.val).trans
      (LinearEquiv.ofEq _ _ h)).toModuleIso

attribute [local irreducible] affineTilde vectorFreeIso coordinates

/-- The comparison preserves the inclusion through the genuine original free-sheaf map. -/
lemma sectionLineCompare_inclusion
    (e : (SheafOfModules.free ι : S.Modules) ≅ SheafOfModules.free κ)
    (i : ι) (j : κ) (L : Chart Γ(S, ⊤) ι i) (N : Chart Γ(S, ⊤) κ j) (h) :
    (sectionLineCompare S e i j L N h).hom ≫ sectionLineInclusion S j N =
      sectionLineInclusion S i L ≫ e.hom := by
  have hv := congrArg Iso.hom (vectorCoordinates_reconstruct S e)
  dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    LinearEquiv.toModuleIso_hom] at hv
  dsimp only [sectionLineCompare, sectionLineInclusion, Functor.mapIso_hom]
  rw [← Category.assoc, ← Functor.map_comp]
  have hm :
      (((functionCoordinates (coordinates S e)).submoduleMap L.val).trans
        (LinearEquiv.ofEq _ _ h)).toModuleIso.hom ≫ ModuleCat.ofHom N.val.subtype =
      ModuleCat.ofHom L.val.subtype ≫
        ModuleCat.ofHom (functionCoordinates (coordinates S e)).toLinearMap := by
    apply ModuleCat.hom_ext
    ext v k
    rfl
  rw [hm, Functor.map_comp, Category.assoc, hv]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The target's split inclusion determines the comparison uniquely. -/
lemma sectionLineCompare_unique
    (e : (SheafOfModules.free ι : S.Modules) ≅ SheafOfModules.free κ)
    (i : ι) (j : κ) (L : Chart Γ(S, ⊤) ι i) (N : Chart Γ(S, ⊤) κ j) (h)
    (a : sectionLineSheaf S i L ⟶ sectionLineSheaf S j N)
    (ha : a ≫ sectionLineInclusion S j N = sectionLineInclusion S i L ≫ e.hom) :
    a = (sectionLineCompare S e i j L N h).hom := by
  apply (cancel_mono (sectionLineInclusion S j N)).mp
  rw [ha, sectionLineCompare_inclusion]

/-- The actual image equalities compose through the recovered original sheaf coordinates. -/
lemma sectionLineImage_trans
    (e : (SheafOfModules.free ι : S.Modules) ≅ SheafOfModules.free κ)
    (d : (SheafOfModules.free κ : S.Modules) ≅ SheafOfModules.free ν)
    (i : ι) (j : κ) (k : ν) (L : Chart Γ(S, ⊤) ι i)
    (N : Chart Γ(S, ⊤) κ j) (P : Chart Γ(S, ⊤) ν k)
    (h : L.val.map (functionCoordinates (coordinates S e)).toLinearMap = N.val)
    (h' : N.val.map (functionCoordinates (coordinates S d)).toLinearMap = P.val) :
    L.val.map (functionCoordinates (coordinates S (e ≪≫ d))).toLinearMap = P.val := by
  rw [coordinates_trans, functionCoordinates_trans]
  change L.val.map ((functionCoordinates (coordinates S d)).toLinearMap.comp
    (functionCoordinates (coordinates S e)).toLinearMap) = P.val
  rw [Submodule.map_comp, h, h']

/-- The actual line comparisons satisfy the cocycle for composed free-sheaf isomorphisms. -/
lemma sectionLineCompare_cocycle
    (e : (SheafOfModules.free ι : S.Modules) ≅ SheafOfModules.free κ)
    (d : (SheafOfModules.free κ : S.Modules) ≅ SheafOfModules.free ν)
    (i : ι) (j : κ) (k : ν) (L : Chart Γ(S, ⊤) ι i)
    (N : Chart Γ(S, ⊤) κ j) (P : Chart Γ(S, ⊤) ν k) (h) (h') :
    sectionLineCompare S e i j L N h ≪≫ sectionLineCompare S d j k N P h' =
      sectionLineCompare S (e ≪≫ d) i k L P (sectionLineImage_trans S e d i j k L N P h h') := by
  apply Iso.ext
  apply sectionLineCompare_unique
  simp only [Iso.trans_hom, Category.assoc, sectionLineCompare_inclusion]
  rw [← Category.assoc, sectionLineCompare_inclusion, Category.assoc]

/-- Choosing the constructed transported line recovers its original sheaf transport. -/
lemma sectionLineCompare_transport
    (e : (SheafOfModules.free ι : S.Modules) ≅ SheafOfModules.free κ)
    (i : ι) (j : κ) (L : Chart Γ(S, ⊤) ι i) (a : Γ(S, ⊤)ˣ) (ha) :
    sectionLineCompare S e i j L
        (linearTransport (functionCoordinates (coordinates S e)) i j L a ha) rfl =
      sectionLineTransport S e i j L a ha := by
  apply Iso.ext
  symm
  apply sectionLineCompare_unique
  exact sectionLineTransport_inclusion S e i j L a ha

end FLT.Mazur.AffineFreeSheafCoordinates
