/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafOpenIsoDetection
public import FLT.Mazur.ModuleSectionIsomorphismTransport

/-!
# The maximal open where a module morphism is invertible

Take the union of all opens where the actual restriction is an isomorphism.
Local detection proves invertibility on this union. Applied to a section map,
this constructs its generator open without assuming a chosen trivialization.
-/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open ModuleSheafOpenIsoDetection
variable {X : Scheme.{u}} {M N : X.Modules}

/-- Restriction transports invertibility to the inverse image of a known isomorphism open. -/
lemma moduleHom_isIso_restrict_preimage (f : M ⟶ N) {Y : Scheme.{u}}
    (g : Y ⟶ X) [IsOpenImmersion g] (U : X.Opens)
    [IsIso ((restrictFunctor U.ι).map f)] :
    IsIso ((restrictFunctor (g ⁻¹ᵁ U).ι).map ((restrictFunctor g).map f)) := by
  apply Hom.isIso_iff_isIso_app.mpr
  intro V
  change IsIso (f.app (g ''ᵁ (g ⁻¹ᵁ U).ι ''ᵁ V))
  exact isIso_app_of_restrict f U _
    ((g.image_mono ((g ⁻¹ᵁ U).ι_image_le V)).trans (g.image_preimage_le U))

/-- The maximal open on which a module-sheaf morphism is an isomorphism. -/
def moduleHomIsoOpen (f : M ⟶ N) : X.Opens :=
  ⨆ U : {U : X.Opens // IsIso ((restrictFunctor U.ι).map f)}, U.val

/-- Every open of invertibility lies in the isomorphism open. -/
lemma le_moduleHomIsoOpen (f : M ⟶ N) (U : X.Opens)
    [h : IsIso ((restrictFunctor U.ι).map f)] : U ≤ moduleHomIsoOpen f :=
  le_iSup_of_le ⟨U, h⟩ le_rfl

/-- Restriction of a module morphism is invertible on its maximal isomorphism open. -/
instance moduleHomIsoOpen_isIso (f : M ⟶ N) :
    IsIso ((restrictFunctor (moduleHomIsoOpen f).ι).map f) := by
  let L := moduleHomIsoOpen f
  let U (i : {U : X.Opens // IsIso ((restrictFunctor U.ι).map f)}) : L.toScheme.Opens :=
    L.ι ⁻¹ᵁ i.val
  apply isIso_of_openCover _ U
  · intro x
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp x.property
    exact ⟨i, hi⟩
  · intro i
    have := i.property
    exact moduleHom_isIso_restrict_preimage f L.ι i.val

/-- Subopens of the isomorphism open are exactly opens of invertibility. -/
lemma le_moduleHomIsoOpen_iff (f : M ⟶ N) (U : X.Opens) :
    U ≤ moduleHomIsoOpen f ↔ IsIso ((restrictFunctor U.ι).map f) := by
  constructor
  · intro h
    apply Hom.isIso_iff_isIso_app.mpr
    intro V
    exact isIso_app_of_restrict f (moduleHomIsoOpen f) _ ((U.ι_image_le V).trans h)
  · intro h
    exact le_moduleHomIsoOpen f U

/-- The nonvanishing open of a section, expressed by its actual generator morphism. -/
def sectionGeneratorOpen (M : X.Modules) (s : Γ(M, ⊤)) : X.Opens :=
  moduleHomIsoOpen (globalSectionHom M s)

/-- The section generates on the open just constructed. -/
instance sectionHom_generatorOpen_isIso (M : X.Modules) (s : Γ(M, ⊤)) :
    IsIso (sectionHom M (sectionGeneratorOpen M s)
      (M.presheaf.map (homOfLE le_top).op s)) := by
  rw [sectionHom_restrict_global]
  dsimp only [sectionGeneratorOpen]
  infer_instance

/-- A known generating open is contained in the canonical generator open. -/
lemma le_sectionGeneratorOpen (M : X.Modules) (s : Γ(M, ⊤)) (U : X.Opens)
    [IsIso (sectionHom M U (M.presheaf.map (homOfLE le_top).op s))] :
    U ≤ sectionGeneratorOpen M s := by
  apply (le_moduleHomIsoOpen_iff _ U).mpr
  have h : IsIso ((restrictUnitIso U.ι).inv ≫
      (restrictFunctor U.ι).map (globalSectionHom M s)) := by
    rw [← sectionHom_restrict_global]
    infer_instance
  exact IsIso.of_isIso_comp_left (restrictUnitIso U.ι).inv _

end FLT.Mazur.FCurve
