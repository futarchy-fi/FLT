/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GenericIdealInjection

/-!
# Dense-open detection on reduced schemes

A section of a reduced scheme which vanishes on a dense open is zero: its
basic open would otherwise meet that dense open. This also detects morphisms
into structure modules, finite free modules, and the actual ideal sums.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.ReducedDenseRestriction

open FLT.Mazur.FCurve FLT.Mazur.FCurve.CoherentDevissage
open FLT.Mazur.CoherentGenericCoordinates FLT.Mazur.CommonIdealDirectSum
open FLT.Mazur.AnnihilatorSubsheaf

variable {X : Scheme} [IsReduced X]

/-- Dense restriction detects sections of the reduced structure sheaf. -/
theorem section_eq_zero (D : X.Opens) (hD : Dense (D : Set X))
    (U : X.Opens) (s : Γ(X, U))
    (hs : X.presheaf.map (homOfLE (inf_le_right : D ⊓ U ≤ U)).op s = 0) : s = 0 := by
  apply eq_zero_of_basicOpen_eq_bot s
  apply le_bot_iff.mp
  intro x hx
  have hne : ((X.basicOpen s : X.Opens) : Set X).Nonempty := ⟨x, hx⟩
  obtain ⟨y, hy, hyD⟩ := hD.inter_open_nonempty _ (X.basicOpen s).isOpen hne
  have hz : (D ⊓ U) ⊓ X.basicOpen s = ⊥ := by
    rw [← X.basicOpen_res, hs, X.basicOpen_zero]
  exact (show y ∈ (⊥ : X.Opens) from hz ▸ ⟨⟨hyD, X.basicOpen_le s hy⟩, hy⟩)

/-- Stalks on a dense open detect maps into the structure module. -/
theorem structure_map_eq_zero (D : X.Opens) (hD : Dense (D : Set X))
    {M : X.Modules} (f : M ⟶ structureModule X)
    (hf : ∀ x ∈ D, (stalk x).map f = 0) : f = 0 := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  change f.app U s = 0
  apply section_eq_zero D hD U (f.app U s)
  apply TopCat.Presheaf.section_ext X.sheaf
  intro x hx
  change X.presheaf.germ (D ⊓ U) x hx
    (X.presheaf.map (homOfLE (inf_le_right : D ⊓ U ≤ U)).op (f.app U s)) = _
  erw [map_zero, X.presheaf.germ_res_apply]
  have hz : (structureModule X).presheaf.germ U x hx.2 (f.app U s) = 0 := by
    erw [← TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx.2 f.mapPresheaf]
    change (stalk x).map f _ = 0
    rw [hf x hx.1]
    rfl
  rw [← structureStalkIso_germ, hz, map_zero]

/-- Finite free targets inherit dense-open detection coordinate by coordinate. -/
theorem free_map_eq_zero (D : X.Opens) (hD : Dense (D : Set X))
    {M : X.Modules} (r : ℕ) (f : M ⟶ finiteFree X r)
    (hf : ∀ x ∈ D, (stalk x).map f = 0) : f = 0 := by
  apply (cancel_mono (finiteFreeProductIso X r).hom).mp
  apply Limits.Pi.hom_ext
  intro i
  rw [zero_comp, zero_comp]
  apply structure_map_eq_zero D hD
  intro x hx
  simp only [Functor.map_comp, hf x hx, zero_comp]

/-- An ideal-sum map which is monic on a dense open is globally monic. -/
theorem mono_of_dense_stalk_mono (D : X.Opens) (hD : Dense (D : Set X))
    (I : X.IdealSheafData) (r : ℕ) {N : X.Modules} (f : idealSum I r ⟶ N)
    (hf : ∀ x ∈ D, Mono ((stalk x).map f)) : Mono f := by
  apply Preadditive.mono_of_cancel_zero
  intro M a ha
  apply (cancel_mono (sumInclusion I r)).mp
  rw [zero_comp]
  apply free_map_eq_zero D hD r
  intro x hx
  have := hf x hx
  have hz : (stalk x).map a = 0 := by
    apply (cancel_mono ((stalk x).map f)).mp
    rw [zero_comp, ← Functor.map_comp, ha, Functor.map_zero]
  simp only [Functor.map_comp, hz, zero_comp]

end FLT.Mazur.ReducedDenseRestriction
