/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleLineBundle

/-!
# Transport of the isomorphism open

Restriction identifies the actual isomorphism open with its inverse image.
Arbitrary pullback preserves invertibility on that inverse image.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X Y : Scheme.{u}} {L M N : X.Modules}

/-- Precomposition by an isomorphism preserves the isomorphism open. -/
lemma moduleHomIsoOpen_iso_comp (e : L ≅ M) (a : M ⟶ N) :
    moduleHomIsoOpen (e.hom ≫ a) = moduleHomIsoOpen a := by
  apply le_antisymm
  · apply (le_moduleHomIsoOpen_iff _ _).mpr
    have h : IsIso ((restrictFunctor (moduleHomIsoOpen (e.hom ≫ a)).ι).map
        (e.hom ≫ a)) := inferInstance
    rw [Functor.map_comp] at h
    exact IsIso.of_isIso_comp_left
      ((restrictFunctor (moduleHomIsoOpen (e.hom ≫ a)).ι).map e.hom) _
  · apply (le_moduleHomIsoOpen_iff _ _).mpr
    rw [Functor.map_comp]
    infer_instance

/-- A commuting square of coefficient isomorphisms preserves the isomorphism open. -/
lemma moduleHomIsoOpen_square {L' M' : X.Modules} (a : L ⟶ M) (b : L' ⟶ M')
    (e : L ≅ L') (e' : M ≅ M') (h : a ≫ e'.hom = e.hom ≫ b) :
    moduleHomIsoOpen a = moduleHomIsoOpen b := by
  rw [← moduleHomIsoOpen_comp_iso a e', h, moduleHomIsoOpen_iso_comp]

/-- Restriction along an open immersion gives exactly the inverse-image open. -/
lemma moduleHomIsoOpen_restrict (a : L ⟶ M) (j : Y ⟶ X) [IsOpenImmersion j] :
    moduleHomIsoOpen ((restrictFunctor j).map a) = j ⁻¹ᵁ moduleHomIsoOpen a := by
  apply le_antisymm
  · let V := moduleHomIsoOpen ((restrictFunctor j).map a)
    have hi : IsIso ((restrictFunctor (V.ι ≫ j)).map a) := by
      apply Hom.isIso_iff_isIso_app.mpr
      intro W
      change IsIso (a.app ((V.ι ≫ j) ''ᵁ W))
      rw [Scheme.Hom.comp_image]
      exact inferInstanceAs (IsIso (((restrictFunctor V.ι).map
        ((restrictFunctor j).map a)).app W))
    have him := moduleHom_isIso_restrict_opensRange a (V.ι ≫ j)
    have hle := le_moduleHomIsoOpen a (V.ι ≫ j).opensRange
    intro x hx
    apply hle
    exact ⟨⟨x, hx⟩, rfl⟩
  · apply (le_moduleHomIsoOpen_iff _ _).mpr
    exact moduleHom_isIso_restrict_preimage a j _

/-- Pullback preserves invertibility over every open of invertibility. -/
lemma preimage_moduleHomIsoOpen_le (a : L ⟶ M) (f : Y ⟶ X) :
    f ⁻¹ᵁ moduleHomIsoOpen a ≤ moduleHomIsoOpen ((pullback f).map a) := by
  apply (le_moduleHomIsoOpen_iff _ _).mpr
  let U := moduleHomIsoOpen a
  have h := modulePullbackRestrictIso_naturality f (f ∣_ U) (f ⁻¹ᵁ U).ι U.ι
    (morphismRestrict_ι f U).symm a
  have hi : IsIso ((restrictFunctor (f ⁻¹ᵁ U).ι).map ((pullback f).map a) ≫
      (modulePullbackOpenIso f U M).hom) := by
    rw [show (modulePullbackOpenIso f U M).hom =
      (modulePullbackRestrictIso f (f ∣_ U) (f ⁻¹ᵁ U).ι U.ι
        (morphismRestrict_ι f U).symm M).hom from rfl, h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (modulePullbackOpenIso f U M).hom

/-- Every generating open pulls back to a generating open of the pulled-back section. -/
lemma preimage_sectionGeneratorOpen_le (f : Y ⟶ X) (s : Γ(M, ⊤)) :
    f ⁻¹ᵁ sectionGeneratorOpen M s ≤
      sectionGeneratorOpen ((pullback f).obj M) (pullGlobal f M s) := by
  dsimp only [sectionGeneratorOpen]
  rw [globalSectionHom_pullGlobal]
  exact (preimage_moduleHomIsoOpen_le _ f).trans_eq
    (moduleHomIsoOpen_iso_comp (modulePullbackUnitIso f).symm
      ((pullback f).map (globalSectionHom M s))).symm

end FLT.Mazur.FCurve
