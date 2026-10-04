/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSectionUnit
public import FLT.Mazur.ProjectiveGeneration
public import FLT.Mazur.ModuleSheafMorphismGluing

/-!
# Global generation detected by local section morphisms

If one of the given global sections generates on each member of an open
cover, their actual global evaluation morphism is an epimorphism.
-/

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X : Scheme.{u}}

/-- Local generating section morphisms imply epimorphic global evaluation. -/
theorem globalEvaluation_epi_of_sectionHom_cover {M : X.Modules} {κ : Type u}
    (s : κ → Γ(M, ⊤)) {ι : Type v} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (a : ι → κ)
    (hs : ∀ i, Epi (sectionHom M (U i)
      (M.presheaf.map (homOfLE le_top).op (s (a i))))) :
    Epi (ProjectiveSpace.globalEvaluation M s) where
  left_cancellation {N} f g h := by
    apply ModuleSheafMorphismGluing.hom_ext_restrict U hU
    intro i
    have := hs i
    apply (cancel_epi (sectionHom M (U i)
      (M.presheaf.map (homOfLE le_top).op (s (a i))))).mp
    rw [sectionHom_comp, sectionHom_comp]
    congr 1
    exact ProjectiveSpace.globalEvaluation_cancel s f g h (a i) (U i)

/-- A cover of trivializations by the given sections suffices for global generation. -/
theorem globalEvaluation_epi_of_sectionHom_isIso {M : X.Modules} {κ : Type u}
    (s : κ → Γ(M, ⊤)) {ι : Type v} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (a : ι → κ)
    (hs : ∀ i, IsIso (sectionHom M (U i)
      (M.presheaf.map (homOfLE le_top).op (s (a i))))) :
    Epi (ProjectiveSpace.globalEvaluation M s) := by
  apply globalEvaluation_epi_of_sectionHom_cover s U hU a
  intro i
  have := hs i
  infer_instance

end FLT.Mazur.FCurve
