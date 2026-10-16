/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonTopNodeGraphBranchMaps

/-!
# Original ring generators of the higher graph

The source ring and both target coordinates generate the full graph as a
ring. This statement does not require flatness or a preceding action law.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
variable (R : Type) [CommRing R] (m : ℕ)
variable (u v : ((Ring R (m + 1))[T;T⁻¹])ˣ)
local notation "S" => Ring R (m + 1)
local notation "e" => parameter R (m + 1)
local notation "B" => ChartRing (e)
local notation "L" => (S)[T;T⁻¹]
local notation "G" => topNodeGraphAlgebra R m u v
local notation "s" => topNodeGraphSource R m u v
local notation "d" => topNodeGraphTarget R m u v
local notation "β" => stageNodeBranchPair R (m + 1)
local notation "F" => stageNodeBranchSubstitution R (m + 1) u v

/-- The source ring and two original target coordinates generate every graph function. -/
theorem topNodeGraph_subring_eq_top (D : Subring (G))
    (hs : ∀ z : B, (s) z ∈ D)
    (hx : (d) (leftCoordinate (e)) ∈ D)
    (hy : (d) (rightCoordinate (e)) ∈ D) : D = ⊤ := by
  let A : Subalgebra (S) (G) :=
    { D with
      algebraMap_mem' := fun r ↦ by
        change algebraMap (S) (G) r ∈ D
        simpa only [AlgHom.commutes] using hs (algebraMap (S) (B) r) }
  have hd : (d).range ≤ A := (range_le_iff_coordinates (e) (d) A).mpr ⟨hx, hy⟩
  have he : (G) ≤ A.map (G).val := by
    apply sup_le
    · rintro z ⟨w, rfl⟩
      exact ⟨(s) w, hs w, rfl⟩
    · rintro z ⟨w, rfl⟩
      exact ⟨(d) w, hd ⟨w, rfl⟩, rfl⟩
  apply top_unique
  intro z _
  obtain ⟨w, hw, heq⟩ := he z.property
  have hwz : w = z := Subtype.ext heq
  exact hwz ▸ hw

/-- Lifting those original generators suffices for a surjection onto the whole graph. -/
theorem topNodeGraph_surjective_of_generators {T : Type*} [CommRing T]
    (f : T →+* (G)) (hs : ∀ z : B, (s) z ∈ f.range)
    (hx : (d) (leftCoordinate (e)) ∈ f.range)
    (hy : (d) (rightCoordinate (e)) ∈ f.range) : Function.Surjective f := by
  have he := topNodeGraph_subring_eq_top R m u v f.range hs hx hy
  intro z
  have hz : z ∈ f.range := he.symm ▸ (show z ∈ (⊤ : Subring (G)) from trivial)
  exact hz

end FLT.Mazur.PolygonInfinitesimalStages
