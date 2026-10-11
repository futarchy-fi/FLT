/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedEqualityInitialEndpoints
public import FLT.Mazur.WeierstrassDividedEqualityComponentEndpoints
public import FLT.Mazur.WeierstrassDividedPositiveEqualityBranchIndices

/-!
# Complete positive-start branches in the original equality-depth fiber

An initial component followed by all adjacent components gives each branch.
The endpoints are the original initial and retained attachment sections.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "p" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  (finiteGlobalStructure hπ data (s + 1) hs)
local notation "N" => equalityNodeOverSection hπ data D s hs hk
local notation "b" => positiveEqualityBranchNode start s hstart

/-- The original initial component followed by the entire adjacent chain. -/
def positiveEqualityBranchComponent (j : Fin (s + 1)) (i : Fin 2) :
    PolygonPinching.component K ⟶ Over.mk p :=
  if h : j.val = 0 then equalityInitialOverComponent hπ data D s hs hstart hk i
  else finalAdjacentOverComponent hπ data D s hs hk ⟨j.val - 1, by omega⟩ i

/-- The first component is the complete original initial projective line. -/
theorem positiveEqualityBranchComponent_initial (i : Fin 2) :
    positiveEqualityBranchComponent hπ data D s hs hstart hk 0 i =
      equalityInitialOverComponent hπ data D s hs hstart hk i := by
  simp only [positiveEqualityBranchComponent, Fin.val_zero, dite_true]

/-- Subsequent positions recover the complete original adjacent components. -/
theorem positiveEqualityBranchComponent_adjacent (j : Fin s) (i : Fin 2) :
    positiveEqualityBranchComponent hπ data D s hs hstart hk ⟨j.val + 1, by omega⟩ i =
      finalAdjacentOverComponent hπ data D s hs hk j i := by
  rw [positiveEqualityBranchComponent, dite_eq_right (show ¬j.val + 1 = 0 by omega)]
  rfl

/-- Each zero is the preceding original branch attachment. -/
@[reassoc] theorem positiveEqualityBranchComponent_zero (j : Fin (s + 1)) (i : Fin 2) :
    ProjectiveLine.zeroSection K ≫
        positiveEqualityBranchComponent hπ data D s hs hstart hk j i =
      N (b ⟨j.val, by omega⟩ i) := by
  by_cases hj : j.val = 0
  · have he : j = 0 := Fin.ext hj
    subst j
    rw [positiveEqualityBranchComponent_initial, equalityInitialOverComponent_zero]
    rfl
  · rw [positiveEqualityBranchComponent, dite_eq_right hj,
      equalityAdjacentOverComponent_zero, positiveEqualityBranchNode, dite_eq_right hj]

/-- Each infinity is the next original branch attachment. -/
@[reassoc] theorem positiveEqualityBranchComponent_infinity (j : Fin (s + 1)) (i : Fin 2) :
    ProjectiveLine.infinitySection K ≫
        positiveEqualityBranchComponent hπ data D s hs hstart hk j i =
      N (b ⟨j.val + 1, by omega⟩ i) := by
  rw [positiveEqualityBranchNode_retained]
  by_cases hj : j.val = 0
  · have he : j = 0 := Fin.ext hj
    subst j
    exact equalityInitialOverComponent_infinity hπ data D s hs hstart hk i
  · rw [positiveEqualityBranchComponent, dite_eq_right hj,
      equalityAdjacentOverComponent_infinity]
    congr 3
    apply Fin.ext
    change j.val - 1 + 1 = j.val
    omega

variable (hp : 2 * (start + s + 1) = depth)

/-- The terminal zero is the final attachment on the first full branch. -/
@[reassoc] theorem positiveEqualityTerminal_zero :
    ProjectiveLine.zeroSection K ≫ equalityTerminalOverComponent hπ data D s hs hk hp =
      N (b ⟨s + 1, by omega⟩ 0) := by
  rw [positiveEqualityBranchNode_retained start s hstart ⟨s, by omega⟩]
  exact equalityTerminalOverComponent_zero hπ data D s hs hk hp

/-- The terminal infinity is the final attachment on the second full branch. -/
@[reassoc] theorem positiveEqualityTerminal_infinity :
    ProjectiveLine.infinitySection K ≫ equalityTerminalOverComponent hπ data D s hs hk hp =
      N (b ⟨s + 1, by omega⟩ 1) := by
  rw [positiveEqualityBranchNode_retained start s hstart ⟨s, by omega⟩]
  exact equalityTerminalOverComponent_infinity hπ data D s hs hk hp

end FLT.Mazur.WeierstrassDividedDepth
