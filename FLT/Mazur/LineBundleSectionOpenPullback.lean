/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleHomTrivialOpen

/-!
# Exact pullback of line-bundle section opens

The isomorphism open of a map between line bundles commutes with arbitrary
scheme pullback. This follows locally from the basic-open calculation for
scalar multiplication; no flatness or reducedness hypothesis is needed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X Y : Scheme.{u}} {L M : X.Modules}

/-- Isomorphism opens commute with arbitrary pullback for maps of line bundles. -/
theorem moduleHomIsoOpen_pullback (a : L ⟶ M)
    (hL : LocallyFreeRankOne L) (hM : LocallyFreeRankOne M) (f : Y ⟶ X) :
    moduleHomIsoOpen ((pullback f).map a) = f ⁻¹ᵁ moduleHomIsoOpen a := by
  apply le_antisymm _ (preimage_moduleHomIsoOpen_le a f)
  intro y hy
  obtain ⟨U, hyU, ⟨e⟩⟩ := hL (f y)
  obtain ⟨V, hyV, ⟨e'⟩⟩ := hM (f y)
  let W := U ⊓ V
  let b := (restrictFunctor W.ι).map a
  have he := moduleHomIsoOpen_pullback_of_trivial b
    (ModuleSheafTensor.restrictTrivialization (show W ≤ U from inf_le_left) e)
    (ModuleSheafTensor.restrictTrivialization (show W ≤ V from inf_le_right) e') (f ∣_ W)
  have hs := moduleHomIsoOpen_square
    ((restrictFunctor (f ⁻¹ᵁ W).ι).map ((pullback f).map a))
    ((pullback (f ∣_ W)).map b)
    (modulePullbackOpenIso f W L) (modulePullbackOpenIso f W M)
    (modulePullbackRestrictIso_naturality f (f ∣_ W) (f ⁻¹ᵁ W).ι W.ι
      (morphismRestrict_ι f W).symm a)
  rw [moduleHomIsoOpen_restrict, he, moduleHomIsoOpen_restrict] at hs
  have hm : (⟨y, hyU, hyV⟩ : (f ⁻¹ᵁ W).toScheme) ∈
      (f ⁻¹ᵁ W).ι ⁻¹ᵁ moduleHomIsoOpen ((pullback f).map a) := hy
  rw [hs] at hm
  rw [← Scheme.Hom.comp_preimage, morphismRestrict_ι, Scheme.Hom.comp_preimage] at hm
  exact hm

/-- A pulled-back section generates exactly over the inverse image of its generator open. -/
theorem sectionGeneratorOpen_pullGlobal (hM : LocallyFreeRankOne M)
    (f : Y ⟶ X) (s : Γ(M, ⊤)) :
    sectionGeneratorOpen ((pullback f).obj M) (pullGlobal f M s) =
      f ⁻¹ᵁ sectionGeneratorOpen M s := by
  dsimp only [sectionGeneratorOpen]
  rw [globalSectionHom_pullGlobal]
  exact (moduleHomIsoOpen_iso_comp (modulePullbackUnitIso f).symm _).trans
    (moduleHomIsoOpen_pullback _ structureModule_locallyFreeRankOne hM f)

end FLT.Mazur.FCurve
