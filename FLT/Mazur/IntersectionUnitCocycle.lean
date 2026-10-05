/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteIntersectionCocycleUnits

/-!
# An ambient cocycle from intersection-indexed units

Units on finite intersections, natural under adding labels and satisfying
triple multiplication, define a cocycle on the singleton charts.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.FCurve.ModuleSheafUnitCocycle

namespace FLT.Mazur.Approximation

universe u

/-- The intersection label for two original charts. -/
def pairChartSet {ι : Type u} (i j : ι) : NonemptyChartSet ι :=
  unionChartSet (singletonChartSet i) (singletonChartSet j)

@[simp] theorem mem_pairChartSet {ι : Type u} (i j k : ι) :
    k ∈ (pairChartSet i j).val ↔ k = i ∨ k = j := by
  classical
  simp [pairChartSet, unionChartSet, singletonChartSet]

/-- Any set containing two labels contains their pair intersection index. -/
theorem pairChartSet_le {ι : Type u} {i j : ι} {s : NonemptyChartSet ι}
    (hi : i ∈ s.val) (hj : j ∈ s.val) : pairChartSet i j ≤ s := by
  intro k hk
  rcases (mem_pairChartSet i j k).mp hk with rfl | rfl <;> assumption

variable {X : Scheme.{u}} {ι : Type u} (O : NonemptyChartSet ι → X.Opens)
  (hanti : Antitone O) (hunion : ∀ s t, O (unionChartSet s t) = O s ⊓ O t)
  (y : ∀ s, IntersectionPair s → Γ(X, O s)ˣ)
  (hnat : ∀ {s t} (h : s ≤ t) (k : IntersectionPair s),
    res (hanti h) (y s k : Γ(X, O s)) =
      (y t (intersectionPairMap (homOfLE h) k) : Γ(X, O t)))
  (hmul : ∀ s (k : IntersectionTriple s),
    y s (k.1, k.2.1) * y s (k.2.1, k.2.2) = y s (k.1, k.2.2))

/-- Restrict an indexed transition unit to a smaller ambient open. -/
def intersectionUnitOnOpen (s : NonemptyChartSet ι) (k : IntersectionPair s)
    (V : X.Opens) (h : V ≤ O s) : Γ(X, V)ˣ :=
  Units.map (res h).toMonoidHom (y s k)

include hnat in
/-- Enlarging the label set preserves the transition on every smaller open. -/
theorem intersectionUnitOnOpen_naturality {s t : NonemptyChartSet ι} (h : s ≤ t)
    (k : IntersectionPair s) (V : X.Opens) (hV : V ≤ O t) :
    intersectionUnitOnOpen O y s k V (hV.trans (hanti h)) =
      intersectionUnitOnOpen O y t (intersectionPairMap (homOfLE h) k) V hV := by
  apply Units.ext
  change res _ (y s k : Γ(X, O s)) = res _ (y t _ : Γ(X, O t))
  rw [← hnat h k, res_res]

include hmul in
/-- Repeated-label multiplication forces diagonal normalization. -/
theorem intersectionUnit_diagonal (s : NonemptyChartSet ι) (i : {i // i ∈ s.val}) :
    y s (i, i) = 1 := by
  have h := hmul s (i, i, i)
  exact mul_left_cancel (h.trans (mul_one _).symm)

/-- Pairwise transition on any common subopen of two singleton charts. -/
def singletonTransitionUnit (i j : ι) (V : X.Opens)
    (hi : V ≤ O (singletonChartSet i)) (hj : V ≤ O (singletonChartSet j)) : Γ(X, V)ˣ :=
  intersectionUnitOnOpen O y (pairChartSet i j)
    (⟨i, by simp⟩, ⟨j, by simp⟩) V (by rw [pairChartSet, hunion]; exact le_inf hi hj)

include hnat in
/-- A pair transition can be computed in any larger intersection chart. -/
theorem singletonTransitionUnit_eq (i j : ι) (V : X.Opens)
    (hi : V ≤ O (singletonChartSet i)) (hj : V ≤ O (singletonChartSet j))
    (s : NonemptyChartSet ι) (his : i ∈ s.val) (hjs : j ∈ s.val) (hV : V ≤ O s) :
    singletonTransitionUnit O hunion y i j V hi hj =
      intersectionUnitOnOpen O y s (⟨i, his⟩, ⟨j, hjs⟩) V hV :=
  intersectionUnitOnOpen_naturality O hanti y hnat (pairChartSet_le his hjs) _ V hV

/-- The intersection equations give the full ambient unit cocycle. -/
def intersectionUnitsCocycle : Cocycle (fun i ↦ O (singletonChartSet i)) where
  unit := singletonTransitionUnit O hunion y
  natural i j V W h hi hj := by
    change res h (res _ _) = res _ _
    rw [res_res]
  refl i V h := by
    unfold singletonTransitionUnit intersectionUnitOnOpen
    rw [intersectionUnit_diagonal O y hmul]
    exact map_one _
  cocycle i j k V hi hj hk := by
    let s := unionChartSet (pairChartSet i j) (singletonChartSet k)
    have his : i ∈ s.val := by simp [s, unionChartSet]
    have hjs : j ∈ s.val := by simp [s, unionChartSet]
    have hks : k ∈ s.val := by simp [s, unionChartSet, singletonChartSet]
    have hV : V ≤ O s := by
      dsimp [s]
      rw [hunion, pairChartSet, hunion]
      exact le_inf (le_inf hi hj) hk
    rw [singletonTransitionUnit_eq O hanti hunion y hnat i j V hi hj s his hjs hV,
      singletonTransitionUnit_eq O hanti hunion y hnat j k V hj hk s hjs hks hV,
      singletonTransitionUnit_eq O hanti hunion y hnat i k V hi hk s his hks hV]
    unfold intersectionUnitOnOpen
    rw [← map_mul, hmul s (⟨i, his⟩, ⟨j, hjs⟩, ⟨k, hks⟩)]

end FLT.Mazur.Approximation
