/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFreeChartTransitions
public import Mathlib.AlgebraicGeometry.Cover.Directed

/-!
# An affine basis of actual finite free charts

All affine opens carrying a finite free chart form a basis whenever the sheaf
is locally finite free. In particular the atlas includes enough common
refinements, without requiring constant rank or compactness of the base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.AffineFiniteFreeAtlas
open FCurve FiniteFreeChartTransitions
variable {X : Scheme.{u}} (M : X.Modules)

/-- An affine open on which the actual sheaf admits finite free coordinates. -/
def Good (U : X.Opens) : Prop :=
  IsAffineOpen U ∧ ∃ (ι : Type u), Finite ι ∧
    Nonempty (M.restrict U.ι ≅ SheafOfModules.free ι)

/-- The atlas indexes opens rather than choices of their coordinates. -/
abbrev Index := {U : X.Opens // Good M U}

instance (i : Index M) : IsAffine i.val.toScheme := i.property.1

/-- A chosen finite coordinate type for an actual affine free chart. -/
def coordinates (i : Index M) : Type u := i.property.2.choose

instance (i : Index M) : Finite (coordinates M i) := i.property.2.choose_spec.1

/-- Actual sheaf coordinates on each affine free open. -/
def chart (i : Index M) :
    M.restrict i.val.ι ≅ SheafOfModules.free (coordinates M i) :=
  i.property.2.choose_spec.2.some

/-- The inclusion of affine free opens into all opens of the base. -/
def opens : Index M ⥤ X.Opens := (Subtype.mono_coe _).functor

/-- Affine free neighborhoods refine every open neighborhood. -/
lemma exists_mem_le (hM : LocallyFiniteFree M) {x : X} {U : X.Opens} (hx : x ∈ U) :
    ∃ i : Index M, x ∈ i.val ∧ i.val ≤ U := by
  obtain ⟨V, hxV, ι, hι, ⟨e⟩⟩ := hM x
  obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ U ⊓ V from ⟨hx, hxV⟩)
  exact ⟨⟨W, hW, ι, hι, ⟨refineChart M (le_trans hWV inf_le_right) e⟩⟩,
    hxW, le_trans hWV inf_le_left⟩

/-- The actual affine free chart opens form a basis of the base topology. -/
lemma isBasis (hM : LocallyFiniteFree M) :
    Opens.IsBasis (Set.range (fun i : Index M ↦ i.val)) := by
  rw [Opens.isBasis_iff_nbhd]
  intro U x hx
  obtain ⟨i, hi, hle⟩ := exists_mem_le M hM hx
  exact ⟨i.val, ⟨i, rfl⟩, hi, hle⟩

/-- Every intersection has an affine free refinement around each of its points. -/
lemma common_refinement (hM : LocallyFiniteFree M) (i j : Index M) {x : X}
    (hi : x ∈ i.val) (hj : x ∈ j.val) :
    ∃ k : Index M, x ∈ k.val ∧ k ≤ i ∧ k ≤ j := by
  obtain ⟨k, hk, hle⟩ := exists_mem_le M hM (show x ∈ i.val ⊓ j.val from ⟨hi, hj⟩)
  exact ⟨k, hk, show k.val ≤ i.val from hle.trans inf_le_left,
    show k.val ≤ j.val from hle.trans inf_le_right⟩

end FLT.Mazur.AffineFiniteFreeAtlas
