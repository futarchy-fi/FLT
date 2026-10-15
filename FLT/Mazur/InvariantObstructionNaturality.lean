/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.InvariantSectionObstruction

/-!
# Restriction of invariant lifting obstructions

A commuting map of restriction-and-difference diagrams induces an actual map
on obstruction groups. This allows local correction problems to be compared
without choosing compatible lifts or identifying the two independent arrows.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.InvariantSectionObstruction
variable {A B C A' B' C' : Type*}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
  (ρ : A →+ B) (δ : A →+ C) (ρ' : A' →+ B') (δ' : A' →+ C')
  (a : A →+ A') (b : B →+ B') (c : C →+ C')
  (hρ : ∀ x, ρ' (a x) = b (ρ x)) (hδ : ∀ x, δ' (a x) = c (δ x))

include hρ hδ in
/-- Restriction sends every permitted correction to a permitted correction. -/
theorem corrections_map_le :
    corrections ρ δ ≤ (corrections ρ' δ').comap c := by
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨a x, ?_, hδ x⟩
  change ρ' (a x) = 0
  rw [hρ, show ρ x = 0 from hx, map_zero]

/-- The induced map on the full obstruction groups. -/
def map : C ⧸ corrections ρ δ →+ C' ⧸ corrections ρ' δ' :=
  QuotientAddGroup.map _ _ c (corrections_map_le ρ δ ρ' δ' a b c hρ hδ)

/-- Defects of actual source sections commute with restriction. -/
theorem map_defect (x : A) :
    map ρ δ ρ' δ' a b c hρ hδ (defect ρ δ x) = defect ρ' δ' (a x) := by
  change (QuotientAddGroup.mk' (corrections ρ' δ')) (c (δ x)) =
    (QuotientAddGroup.mk' (corrections ρ' δ')) (δ' (a x))
  rw [hδ]

/-- Obstructions commute with restriction, independently of the chosen source lifts. -/
theorem map_obstruction (hs : Function.Surjective ρ) (hs' : Function.Surjective ρ')
    (y : B) :
    map ρ δ ρ' δ' a b c hρ hδ (obstruction ρ δ hs y) =
      obstruction ρ' δ' hs' (b y) := by
  obtain ⟨x, rfl⟩ := hs y
  rw [obstruction_restrict, map_defect, ← hρ, obstruction_restrict]

include hρ hδ in
/-- A vanished obstruction remains zero after restriction. -/
theorem obstruction_zero_of_map (hs : Function.Surjective ρ)
    (hs' : Function.Surjective ρ') (y : B) (hy : obstruction ρ δ hs y = 0) :
    obstruction ρ' δ' hs' (b y) = 0 := by
  rw [← map_obstruction ρ δ ρ' δ' a b c hρ hδ hs hs', hy, map_zero]

end FLT.Mazur.InvariantSectionObstruction
