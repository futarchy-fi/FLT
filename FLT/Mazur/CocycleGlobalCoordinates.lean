/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafUnitCocycleRestrict

/-!
# Global cocycle sections from finite chart coordinates

Coordinates satisfying the transition equation on each pairwise intersection
construct an actual global section. Equality can be tested on these coordinates.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.FCurve.ModuleSheafUnitCocycle.Cocycle

universe u

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (g : Cocycle U)

/-- The coordinate of a global cocycle section on a subopen of a chart. -/
def globalCoordinate (s : g.sections ⊤) (i : ι) (V : X.Opens) (h : V ≤ U i) : Γ(X, V) :=
  res (le_inf le_top h) (s.val i)

/-- Global coordinates commute with restriction. -/
theorem globalCoordinate_restrict (s : g.sections ⊤) (i : ι)
    {V W : X.Opens} (h : V ≤ U i) (hWV : W ≤ V) :
    res hWV (g.globalCoordinate s i V h) =
      g.globalCoordinate s i W (hWV.trans h) := res_res _ _ _

/-- Global coordinates satisfy the actual cocycle transition equation. -/
theorem globalCoordinate_transition (s : g.sections ⊤) (i j : ι)
    (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j) :
    g.globalCoordinate s i V hi =
      (g.unit i j V hi hj : Γ(X, V)) * g.globalCoordinate s j V hj :=
  s.property i j V (le_inf le_top hi) (le_inf le_top hj)

/-- Pairwise compatible chart functions give an actual global section. -/
def globalSectionOfCoordinates (a : ∀ i, Γ(X, U i))
    (ha : ∀ i j, res inf_le_left (a i) =
      (g.unit i j (U i ⊓ U j) inf_le_left inf_le_right : Γ(X, U i ⊓ U j)) *
        res inf_le_right (a j)) : g.sections ⊤ :=
  ⟨fun i ↦ res inf_le_right (a i), by
    intro i j V hi hj
    have hV : V ≤ U i ⊓ U j := le_inf (hi.trans inf_le_right) (hj.trans inf_le_right)
    have h := congrArg (res hV) (ha i j)
    simpa only [map_mul, res_res, g.natural] using h⟩

/-- The constructed section has exactly its prescribed chart coordinates. -/
theorem globalSectionOfCoordinates_coordinate (a : ∀ i, Γ(X, U i))
    (ha : ∀ i j, res inf_le_left (a i) =
      (g.unit i j (U i ⊓ U j) inf_le_left inf_le_right : Γ(X, U i ⊓ U j)) *
        res inf_le_right (a j)) (i : ι) :
    g.globalCoordinate (g.globalSectionOfCoordinates a ha) i (U i) le_rfl = a i := by
  exact (res_res _ _ _).trans (res_self _ _)

/-- Chart coordinates determine the global section. -/
theorem globalCoordinate_ext {s t : g.sections ⊤}
    (h : ∀ i, g.globalCoordinate s i (U i) le_rfl =
      g.globalCoordinate t i (U i) le_rfl) : s = t := by
  apply Subtype.ext
  funext i
  have he := congrArg (res (show ⊤ ⊓ U i ≤ U i from inf_le_right)) (h i)
  simpa only [globalCoordinate, res_res, res_self] using he

end FLT.Mazur.FCurve.ModuleSheafUnitCocycle.Cocycle
