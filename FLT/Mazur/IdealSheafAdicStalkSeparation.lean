/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorIdealStalkExt
public import FLT.Mazur.DivisorStalkLength
public import Mathlib.RingTheory.Filtration

/-!
# Stalk separation for ideals invisible on every infinitesimal stage

An ideal contained in every power of a defining ideal has zero stalk on the
closed subscheme. This is the local Krull-intersection input for family uniqueness.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
universe u
namespace FLT.Mazur.FCurve
open AnnihilatorSubsheaf CoherentDevissage
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X : Scheme.{u}}

/-- Containment of ideal sheaves is preserved on their actual stalk ideals. -/
theorem stalkIdeal_mono {I J : X.IdealSheafData} (h : I ≤ J) (x : X) :
    stalkIdeal I x ≤ stalkIdeal J x := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x)
      TopologicalSpace.isOpen_univ
  rw [stalkIdeal_eq_map I x ⟨U, hU⟩ hx, stalkIdeal_eq_map J x ⟨U, hU⟩ hx]
  exact Ideal.map_mono (h ⟨U, hU⟩)

/-- The zero ideal sheaf has zero actual stalk ideal. -/
theorem stalkIdeal_bot (x : X) : stalkIdeal (⊥ : X.IdealSheafData) x = ⊥ := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x)
      TopologicalSpace.isOpen_univ
  rw [stalkIdeal_eq_map _ x ⟨U, hU⟩ hx]
  exact Ideal.map_bot

/-- An ideal invisible on every thickening has zero stalk along the closed subscheme. -/
theorem stalkIdeal_eq_bot_of_le_powers [IsLocallyNoetherian X]
    (I J : X.IdealSheafData) (hJ : ∀ m : ℕ, J ≤ I ^ (m + 1))
    (x : X) (hx : x ∈ I.support) : stalkIdeal J x = ⊥ := by
  apply bot_unique
  rw [← Ideal.iInf_pow_eq_bot_of_isLocalRing (stalkIdeal I x)
    ((mem_support_iff_stalkIdeal_ne_top I x).mp hx)]
  apply le_iInf
  intro m
  cases m with
  | zero => simp only [pow_zero, Ideal.one_eq_top, le_top]
  | succ m =>
    rw [← stalkIdeal_pow]
    exact stalkIdeal_mono (hJ m) x

/-- The actual inclusion of an ideal into the structure stalk is injective. -/
theorem idealStalkInclusion_injective (I : X.IdealSheafData) (x : X) :
    Function.Injective (idealStalkInclusion I x) := by
  apply (structureStalkLinearEquiv x).injective.comp
  exact (AddCommGrpCat.mono_iff_injective ((stalk x).map (idealModuleι I))).mp inferInstance

/-- Vanishing of the actual ideal stalk makes the corresponding ideal-module stalk zero. -/
theorem idealModule_stalk_isZero_of_stalkIdeal_eq_bot
    (I : X.IdealSheafData) (x : X) (hI : stalkIdeal I x = ⊥) :
    Limits.IsZero ((stalk x).obj (idealModule I)) := by
  apply AddCommGrpCat.isZero_iff_subsingleton.mpr
  refine ⟨fun a b ↦ idealStalkInclusion_injective I x ?_⟩
  have hz (v : (idealModule I).presheaf.stalk x) : idealStalkInclusion I x v = 0 := by
    have hv : idealStalkInclusion I x v ∈ stalkIdeal I x := ⟨v, rfl⟩
    simpa only [hI, Ideal.mem_bot] using hv
  rw [hz, hz]

end FLT.Mazur.FCurve
