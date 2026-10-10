/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntersectionSectionLimitCoordinates

/-!
# Gluing descended intersection coordinates

Natural coordinates satisfying the cocycle transition equations produce
actual global sections, with exact recovery of every intersection coordinate.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.FCurve.ModuleSheafUnitCocycle

namespace FLT.Mazur.Approximation

universe u

variable {X : Scheme.{u}} {ι T : Type u} (O : NonemptyChartSet ι → X.Opens)
  (hanti : Antitone O) (hunion : ∀ s t, O (unionChartSet s t) = O s ⊓ O t)
  (g : Cocycle (fun i ↦ O (singletonChartSet i)))
  (y : ∀ s, IntersectionSectionLabel T s → Γ(X, O s))
  (hnat : ∀ {s t} (h : s ≤ t) k, res (hanti h) (y s k) =
    y t (intersectionSectionLabelMap (homOfLE h) k))

/-- The singleton chart index lies in every index containing that chart. -/
theorem singletonChartSet_le_of_mem {s : NonemptyChartSet ι} (i : {i // i ∈ s.val}) :
    singletonChartSet i.val ≤ s := by
  classical
  intro j hj
  have : j = i.val := by simpa [singletonChartSet] using hj
  subst j
  exact i.property

variable (htrans : ∀ s (k : IntersectionPair s) l,
  y s (k.1, l) = (g.unit k.1.val k.2.val (O s)
    (hanti (singletonChartSet_le_of_mem k.1))
    (hanti (singletonChartSet_le_of_mem k.2)) : Γ(X, O s)) * y s (k.2, l))

/-- Natural intersection coordinates glue to a genuine global cocycle section. -/
def intersectionGlobalSection (l : T) : g.sections ⊤ := by
  let a (i : ι) := y (singletonChartSet i) (⟨i, by simp [singletonChartSet]⟩, l)
  apply g.globalSectionOfCoordinates a
  intro i j
  let s := pairChartSet i j
  let ii : {k // k ∈ s.val} := ⟨i, by simp [s]⟩
  let jj : {k // k ∈ s.val} := ⟨j, by simp [s]⟩
  have hW : O (singletonChartSet i) ⊓ O (singletonChartSet j) ≤ O s := by
    simp only [s, pairChartSet, hunion, le_refl]
  have hi := congrArg (res hW)
    (hnat (singletonChartSet_le_of_mem ii) (⟨i, by simp [singletonChartSet, ii]⟩, l))
  have hj := congrArg (res hW)
    (hnat (singletonChartSet_le_of_mem jj) (⟨j, by simp [singletonChartSet, jj]⟩, l))
  change res _ (res _ (a i)) = res hW (y s (ii, l)) at hi
  change res _ (res _ (a j)) = res hW (y s (jj, l)) at hj
  rw [res_res] at hi hj
  rw [hi, htrans s (ii, jj) l, map_mul, g.natural, ← hj]

/-- Every descended intersection coordinate is retained by the glued global section. -/
theorem intersectionGlobalSection_coordinate (l : T) (s : NonemptyChartSet ι)
    (k : {i // i ∈ s.val}) :
    g.globalCoordinate (intersectionGlobalSection O hanti hunion g y hnat htrans l)
      k.val (O s) (hanti (singletonChartSet_le_of_mem k)) = y s (k, l) := by
  change res _ (res _ (y (singletonChartSet k.val)
    (⟨k.val, by simp [singletonChartSet]⟩, l))) = _
  rw [res_res]
  exact hnat (singletonChartSet_le_of_mem k) _

include hunion hnat in
/-- Propositional singleton identifications also recover actual global sections. -/
theorem exists_globalSection_of_intersection_coordinates
    {V : ι → X.Opens} (hV : ∀ i, O (singletonChartSet i) = V i) (G : Cocycle V)
    (hG : ∀ s (k : IntersectionPair s) l,
      y s (k.1, l) = (G.unit k.1.val k.2.val (O s)
        ((hanti (singletonChartSet_le_of_mem k.1)).trans (hV k.1.val).le)
        ((hanti (singletonChartSet_le_of_mem k.2)).trans (hV k.2.val).le) :
          Γ(X, O s)) * y s (k.2, l)) :
    ∃ σ : T → G.sections ⊤, ∀ l s (k : {i // i ∈ s.val}),
      G.globalCoordinate (σ l) k.val (O s)
        ((hanti (singletonChartSet_le_of_mem k)).trans (hV k.val).le) = y s (k, l) := by
  have he : (fun i ↦ O (singletonChartSet i)) = V := funext hV
  subst V
  exact ⟨intersectionGlobalSection O hanti hunion G y hnat hG,
    intersectionGlobalSection_coordinate O hanti hunion G y hnat hG⟩

end FLT.Mazur.Approximation
