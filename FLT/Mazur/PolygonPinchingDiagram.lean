/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveLineEndpoints
public import Mathlib.CategoryTheory.Limits.Over

/-!
# The cyclic pinching span

All objects and morphisms live in schemes over `Spec K`. The normalization has
`n` projective-line components. Each node has two branches: zero on component
`i` and infinity on component `i + 1` modulo `n`. Both branches map to node `i`.
For `n = 1`, this identifies the two distinct endpoints of a single component.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.PolygonPinching

variable (K : Type u) [Field K]

/-- The base point, as a scheme over itself. -/
abbrev point : Over (Spec (CommRingCat.of K)) := Over.mk (𝟙 _)

/-- The specified projective line over the base. -/
abbrev component : Over (Spec (CommRingCat.of K)) := Over.mk (ProjectiveLine.toBase K)

/-- The `n` projective-line components, before pinching. -/
abbrev components (n : ℕ) : Over (Spec (CommRingCat.of K)) :=
  ∐ fun _ : Fin n ↦ component K

/-- Two copies of `Spec K` for each node. `false` labels zero, `true` infinity. -/
abbrev branches (n : ℕ) : Over (Spec (CommRingCat.of K)) :=
  ∐ fun _ : Fin n × Bool ↦ point K

/-- The `n` nodes, each a copy of `Spec K`. -/
abbrev nodes (n : ℕ) : Over (Spec (CommRingCat.of K)) :=
  ∐ fun _ : Fin n ↦ point K

/-- Inclusion of one projective-line component. -/
def componentι (n : ℕ) (i : Fin n) : component K ⟶ components K n :=
  Sigma.ι (fun _ : Fin n ↦ component K) i

/-- Inclusion of one branch of a node. -/
def branchι (n : ℕ) (i : Fin n) (b : Bool) : point K ⟶ branches K n :=
  Sigma.ι (fun _ : Fin n × Bool ↦ point K) (i, b)

/-- Inclusion of one node. -/
def nodeι (n : ℕ) (i : Fin n) : point K ⟶ nodes K n :=
  Sigma.ι (fun _ : Fin n ↦ point K) i

/-- Cyclic successor, including the wrap from the last component to the first. -/
def next {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩

@[simp]
theorem next_val {n : ℕ} (hn : 0 < n) (i : Fin n) :
    (next hn i).val = (i.val + 1) % n := rfl

@[simp]
theorem next_one (hn : 0 < 1) (i : Fin 1) : next hn i = i := Subsingleton.elim _ _

/-- The chosen endpoint of the normalization lying over a branch. -/
def endpoint (n : ℕ) (hn : 0 < n) (i : Fin n) (b : Bool) :
    point K ⟶ components K n :=
  if b then ProjectiveLine.infinitySection K ≫ componentι K n (next hn i)
  else ProjectiveLine.zeroSection K ≫ componentι K n i

/-- The first leg of the pinching span: the endpoints in the normalization. -/
def toComponents (n : ℕ) (hn : 0 < n) : branches K n ⟶ components K n :=
  Sigma.desc (f := fun _ : Fin n × Bool ↦ point K)
    fun ib ↦ endpoint K n hn ib.1 ib.2

/-- The second leg of the pinching span: both branches go to their shared node. -/
def toNodes (n : ℕ) : branches K n ⟶ nodes K n :=
  Sigma.desc (f := fun _ : Fin n × Bool ↦ point K) fun ib ↦ nodeι K n ib.1

@[reassoc (attr := simp)]
theorem branchι_toComponents_zero (n : ℕ) (hn : 0 < n) (i : Fin n) :
    branchι K n i false ≫ toComponents K n hn =
      ProjectiveLine.zeroSection K ≫ componentι K n i := by
  simp [branchι, toComponents, endpoint]

@[reassoc (attr := simp)]
theorem branchι_toComponents_infinity (n : ℕ) (hn : 0 < n) (i : Fin n) :
    branchι K n i true ≫ toComponents K n hn =
      ProjectiveLine.infinitySection K ≫ componentι K n (next hn i) := by
  simp [branchι, toComponents, endpoint]

@[reassoc (attr := simp)]
theorem branchι_toNodes (n : ℕ) (i : Fin n) (b : Bool) :
    branchι K n i b ≫ toNodes K n = nodeι K n i := by
  simp [branchι, toNodes]

/-- The span diagram in schemes over `K`. -/
def diagram (n : ℕ) (hn : 0 < n) :
    WalkingSpan ⥤ Over (Spec (CommRingCat.of K)) :=
  span (toComponents K n hn) (toNodes K n)

/-- In the one-component case the first branch is zero on the only component. -/
theorem one_zero (hn : 0 < 1) :
    branchι K 1 0 false ≫ toComponents K 1 hn =
      ProjectiveLine.zeroSection K ≫ componentι K 1 0 := by simp

/-- In the one-component case the other branch is infinity on that same component. -/
theorem one_infinity (hn : 0 < 1) :
    branchι K 1 0 true ≫ toComponents K 1 hn =
      ProjectiveLine.infinitySection K ≫ componentι K 1 0 := by simp

/-- Both endpoints map to the sole node when `n = 1`. -/
theorem one_same_node :
    branchι K 1 0 false ≫ toNodes K 1 = branchι K 1 0 true ≫ toNodes K 1 := by simp

end FLT.Mazur.PolygonPinching
