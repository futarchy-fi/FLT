/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleHomOpenTransport
public import FLT.Mazur.ModuleSectionRatioBasicOpen

/-!
# Isomorphism opens in trivial coordinates

For multiplication by a function, the isomorphism open is its scheme basic
open. Local ring homomorphisms therefore give exact inverse images of these
opens under arbitrary scheme pullback.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
namespace FLT.Mazur.FCurve
variable {X Y : Scheme.{u}}

/-- The unit section induces the identity of the structure module. -/
lemma globalSectionHom_structure_one :
    globalSectionHom (structureModule X) (1 : Γ(X, ⊤)) = 𝟙 _ := by
  apply globalSection_hom_ext
  simp only [globalSectionHom_top, Hom.id_app, ConcreteCategory.id_apply]

/-- The generator open of a function is its ordinary scheme basic open. -/
lemma sectionGeneratorOpen_structure (r : Γ(X, ⊤)) :
    sectionGeneratorOpen (structureModule X) r = X.basicOpen r := by
  have h : sectionGeneratorOpen (structureModule X) (1 : Γ(X, ⊤)) = ⊤ := by
    apply top_unique
    apply (le_moduleHomIsoOpen_iff _ _).mpr
    rw [globalSectionHom_structure_one]
    infer_instance
  have hr : sectionRatioOn (structureModule X) (1 : Γ(X, ⊤)) ⊤ h.ge r = r := by
    apply (sectionRatioOn_eq_iff _ _ _ _ _ _).mpr
    simp
  have hb := sectionRatioOn_basicOpen (structureModule X) (1 : Γ(X, ⊤)) r ⊤ h.ge
  simpa only [hr, top_inf_eq] using hb.symm

/-- The structure-module comparison sends a pulled-back function to its image. -/
lemma pullGlobal_structure_coordinate (f : Y ⟶ X) (r : Γ(X, ⊤)) :
    (modulePullbackUnitIso f).hom.app ⊤ (pullGlobal f (structureModule X) r) =
      f.appTop r :=
  modulePullbackUnitIso_unit f ⊤ r

/-- Scalar endomorphisms have exactly the expected open after arbitrary pullback. -/
lemma moduleHomIsoOpen_pullback_scalar (f : Y ⟶ X) (r : Γ(X, ⊤)) :
    moduleHomIsoOpen ((pullback f).map (globalSectionHom (structureModule X) r)) =
      f ⁻¹ᵁ moduleHomIsoOpen (globalSectionHom (structureModule X) r) := by
  calc
    _ = sectionGeneratorOpen ((pullback f).obj (structureModule X))
        (pullGlobal f (structureModule X) r) := by
      dsimp only [sectionGeneratorOpen]
      rw [globalSectionHom_pullGlobal]
      exact (moduleHomIsoOpen_iso_comp (modulePullbackUnitIso f).symm _).symm
    _ = sectionGeneratorOpen (structureModule Y) (f.appTop r) := by
      rw [← pullGlobal_structure_coordinate f r]
      exact (sectionGeneratorOpen_iso (modulePullbackUnitIso f) _).symm
    _ = _ := by
      rw [sectionGeneratorOpen_structure, ← Scheme.Hom.preimage_basicOpen_top]
      exact congrArg (f ⁻¹ᵁ ·) (sectionGeneratorOpen_structure r).symm

/-- For morphisms between trivial line bundles, pullback preserves the exact open. -/
lemma moduleHomIsoOpen_pullback_of_trivial {L M : X.Modules} (a : L ⟶ M)
    (e : L ≅ structureModule X) (e' : M ≅ structureModule X) (f : Y ⟶ X) :
    moduleHomIsoOpen ((pullback f).map a) = f ⁻¹ᵁ moduleHomIsoOpen a := by
  let b := e.inv ≫ a ≫ e'.hom
  have hb : b = globalSectionHom (structureModule X) (b.app ⊤ (1 : Γ(X, ⊤))) := by
    apply globalSection_hom_ext
    rw [globalSectionHom_top]
  have h := moduleHomIsoOpen_pullback_scalar f (b.app ⊤ (1 : Γ(X, ⊤)))
  rw [← hb] at h
  have h₁ : moduleHomIsoOpen b = moduleHomIsoOpen a :=
    (moduleHomIsoOpen_iso_comp e.symm _).trans (moduleHomIsoOpen_comp_iso a e')
  have h₂ : moduleHomIsoOpen ((pullback f).map b) =
      moduleHomIsoOpen ((pullback f).map a) := by
    dsimp only [b]
    rw [Functor.map_comp, Functor.map_comp]
    exact (moduleHomIsoOpen_iso_comp ((pullback f).mapIso e.symm) _).trans
      (moduleHomIsoOpen_comp_iso _ ((pullback f).mapIso e'))
  exact h₂.symm.trans (h.trans (congrArg (f ⁻¹ᵁ ·) h₁))


end FLT.Mazur.FCurve
