/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineSectionPullbackCoordinates
public import FLT.Mazur.CoherentSubmoduleEnlargement

/-!
# Regular sections on open pullbacks and composite charts

Open restriction preserves monicity of the original section map. Actual
pullback composition and equal-morphism comparisons transport that statement
to the composite chart, retaining the original section throughout.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.OpenSectionMonicity
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y Z : Scheme.{u}}

/-- Actual open pullback preserves monicity of any sheaf morphism. -/
theorem map_mono (f : X ⟶ Y) [IsOpenImmersion f] {L M : Y.Modules}
    (a : L ⟶ M) [Mono a] : Mono ((pullback f).map a) := by
  have := CoherentSubmoduleEnlargement.restrictMap_mono f a
  have h := (restrictFunctorIsoPullback f).hom.naturality a
  have : Mono ((restrictFunctorIsoPullback f).hom.app L ≫ (pullback f).map a) := by
    rw [← h]
    infer_instance
  exact (mono_comp_iff_of_isIso _ _).mp this

/-- A regular section remains regular on every open chart. -/
theorem pullGlobal_mono (f : X ⟶ Y) [IsOpenImmersion f] (L : Y.Modules)
    (s : Γ(L, ⊤)) [Mono (globalSectionHom L s)] :
    Mono (globalSectionHom _ (pullGlobal f L s)) := by
  have := map_mono f (globalSectionHom L s)
  rw [globalSectionHom_pullGlobal]
  infer_instance

/-- The composition comparison preserves and reflects regularity of the pulled section. -/
theorem comp_iff (f : X ⟶ Y) (g : Y ⟶ Z) (L : Z.Modules) (s : Γ(L, ⊤)) :
    Mono (globalSectionHom _ (pullGlobal (f ≫ g) L s)) ↔
      Mono (globalSectionHom _ (pullGlobal f _ (pullGlobal g L s))) := by
  rw [← pullGlobal_comp_hom, ← globalSectionHom_naturality]
  exact mono_comp_iff_of_mono _ ((pullbackComp f g).hom.app L)

/-- A regular fiber section remains regular on a chart with the specified composite map. -/
theorem composite_mono (f : X ⟶ Y) [IsOpenImmersion f] (g : Y ⟶ Z)
    (k : X ⟶ Z) (h : f ≫ g = k) (L : Z.Modules) (s : Γ(L, ⊤))
    [Mono (globalSectionHom _ (pullGlobal g L s))] :
    Mono (globalSectionHom _ (pullGlobal k L s)) := by
  subst k
  exact (comp_iff f g L s).mpr (pullGlobal_mono f _ _)

end FLT.Mazur.OpenSectionMonicity
