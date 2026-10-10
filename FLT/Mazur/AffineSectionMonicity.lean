/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineSectionPullbackCoordinates
public import FLT.Mazur.WeierstrassFlatSectionRegular

/-!
# Regular affine coordinates give monic section maps

Regularity of an affine global function persists on every open, by flatness
of open immersions. Thus a section in an actual affine line frame is monic
exactly when its scalar is regular, including on nonreduced schemes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
namespace FLT.Mazur.AffineSectionMonicity
open FCurve WeierstrassIntegralChart LineSectionPullbackCoordinates
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X : Scheme.{0}} [IsAffine X]

/-- A regular function on an affine scheme remains regular on an arbitrary open. -/
theorem regular_restrict (a : Γ(X, ⊤)) (ha : IsRegular a) (U : X.Opens) :
    IsRegular (X.presheaf.map U.leTop.op a) := by
  have h := flat_appTop_isRegular U.ι ha
  have ht := flatRingHom_isRegular U.topIso.hom.hom
    (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)) h
  have he : U.topIso.hom (U.ι.appTop a) = X.presheaf.map U.leTop.op a := by
    simp only [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom,
      ← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  rwa [he] at ht

/-- Multiplication by a regular affine function is monic as an actual sheaf map. -/
theorem structure_mono (a : Γ(X, ⊤)) (ha : IsRegular a) :
    Mono (globalSectionHom (structureModule X) a) := by
  apply (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro U r t h
  exact (regular_restrict a ha U.unop).right h

/-- A regular scalar in a genuine affine frame makes the original section monic. -/
theorem mono_of_regular {L : X.Modules} (e : L ≅ structureModule X) (s : Γ(L, ⊤))
    (hs : IsRegular (show Γ(X, ⊤) from e.hom.app ⊤ s)) :
    Mono (globalSectionHom L s) := by
  have := structure_mono _ hs
  exact mono_of_mono_fac (globalSectionHom_naturality L e.hom s)

/-- Affine section monicity is exactly regularity of its actual frame coordinate. -/
theorem mono_iff_regular {L : X.Modules} (e : L ≅ structureModule X) (s : Γ(L, ⊤)) :
    Mono (globalSectionHom L s) ↔ IsRegular (show Γ(X, ⊤) from e.hom.app ⊤ s) :=
  ⟨fun _ ↦ regular_coordinate e s, mono_of_regular e s⟩

end FLT.Mazur.AffineSectionMonicity
