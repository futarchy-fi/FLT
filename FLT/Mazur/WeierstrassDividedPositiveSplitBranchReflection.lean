/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveSplitReflection
public import FLT.Mazur.CyclicPinchingOddReflectionIndices

/-!
# Reflection on the original complete branches and attachments

Resolve cyclic reflection into the original geometric components. Both
chains keep their level and parameter; the exterior reverses and the terminal components exchange.
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
  (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "p" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  (finiteGlobalStructure hπ data (s + 1) hs)
local notation "Z" => positiveSplitCycleComponent hπ data D s hs hstart hk hp
local notation "N" => positiveSplitCycleNormalization hπ data D s hs hstart hk hp
local notation "Q" => positiveSplitCycleNodes hπ data D s hs hstart hk hp
local notation "H" => positiveSplitCycleCocone_isPushout hπ data D s hs hstart hk hp
local notation "ρ" => Iso.hom (ProjectiveLine.endpointReversalOverIso K)

local notation "σ" => positiveSplitReflection hπ data D s hs hstart hk hp
local notation "C" => positiveSplitBranchComponent hπ data D s hs hstart hk hp
local notation "A" => finalNodeOverSection hπ data D s hs hk hp
local notation "b" => positiveSplitBranchNode start s hstart

/-- The complete exterior is fixed with its projective coordinate reversed. -/
@[reassoc] theorem positiveSplitReflection_exterior :
    equalityInitialExteriorOverComponent hπ data D s hs hstart hk ≫ σ =
      ρ ≫ equalityInitialExteriorOverComponent hπ data D s hs hstart hk := by
  have hEq := positiveSplitReflection_component hπ data D s hs hstart hk hp 0
  simpa only [PolygonPinching.reflectIndex_zero, positiveSplitCycleComponent_exterior] using hEq

/-- The full first branch goes to the second at the same level and with the same parameter. -/
@[reassoc] theorem positiveSplitReflection_firstBranch (j : Fin (s + 2)) :
    C j 0 ≫ σ = C j 1 := by
  have hEq := positiveSplitReflection_component hπ data D s hs hstart hk hp
    ⟨j.val + 1, by omega⟩
  rw [PolygonPinching.reflectIndex_oddFirstChain, positiveSplitCycleComponent_first,
    positiveSplitCycleComponent_second, Category.assoc] at hEq
  exact (cancel_epi ρ).mp hEq

/-- The opposite complete branch returns with its original parameter unchanged. -/
@[reassoc] theorem positiveSplitReflection_secondBranch (j : Fin (s + 2)) :
    C j 1 ≫ σ = C j 0 := by
  rw [← positiveSplitReflection_firstBranch hπ data D s hs hstart hk hp j,
    Category.assoc, positiveSplitReflection_involutive, Category.comp_id]

/-- Reflection exchanges the two complete original terminal components. -/
@[reassoc] theorem positiveSplitReflection_terminal :
    finalTerminalOverComponent hπ data D s hs hk hp 0 ≫ σ =
      finalTerminalOverComponent hπ data D s hs hk hp 1 := by
  simpa only [positiveSplitBranchComponent_tail hπ data D s hs hstart hk hp ⟨s, by omega⟩,
    finalBranchComponent_terminal] using
    positiveSplitReflection_firstBranch hπ data D s hs hstart hk hp
      ⟨s + 1, by omega⟩

/-- The common original terminal node is fixed by the whole-model reflection. -/
@[reassoc] theorem positiveSplitReflection_terminalNode : A (.inr ()) ≫ σ = A (.inr ()) := by
  have hEq := positiveSplitReflection_node hπ data D s hs hstart hk hp
    ⟨s + 2, by omega⟩
  simpa only [PolygonPinching.reflectNodeIndex_oddTerminal,
    positiveSplitCycleNodeIndex_terminal] using hEq

/-- First-branch attachments go to the corresponding original second-branch sections. -/
@[reassoc] theorem positiveSplitReflection_firstNode (j : Fin (s + 2)) :
    A (b ⟨j.val, by omega⟩ 0) ≫ σ = A (b ⟨j.val, by omega⟩ 1) := by
  have hEq := positiveSplitReflection_node hπ data D s hs hstart hk hp
    ⟨j.val, by omega⟩
  simpa only [PolygonPinching.reflectNodeIndex_oddFirstChain, positiveSplitCycleNodeIndex_first,
    positiveSplitCycleNodeIndex_second] using hEq

/-- Every opposite attachment returns to its partner, including the terminal pair. -/
@[reassoc] theorem positiveSplitReflection_secondNode (j : Fin (s + 2)) :
    A (b ⟨j.val, by omega⟩ 1) ≫ σ = A (b ⟨j.val, by omega⟩ 0) := by
  rw [← positiveSplitReflection_firstNode hπ data D s hs hstart hk hp j,
    Category.assoc, positiveSplitReflection_involutive, Category.comp_id]

/-- Both original initial projective components are exchanged as entire schemes. -/
@[reassoc] theorem positiveSplitReflection_initial :
    equalityInitialOverComponent hπ data D s hs hstart hk 0 ≫ σ =
      equalityInitialOverComponent hπ data D s hs hstart hk 1 := by
  simpa only [positiveSplitBranchComponent_initial] using
    positiveSplitReflection_firstBranch hπ data D s hs hstart hk hp 0

/-- Every retained adjacent projective component is exchanged at its actual level. -/
@[reassoc] theorem positiveSplitReflection_adjacent (j : Fin s) :
    finalAdjacentOverComponent hπ data D s hs hk j 0 ≫ σ =
      finalAdjacentOverComponent hπ data D s hs hk j 1 := by
  simpa only [positiveSplitBranchComponent_tail hπ data D s hs hstart hk hp
    ⟨j.val, by omega⟩, finalBranchComponent_adjacent] using
    positiveSplitReflection_firstBranch hπ data D s hs hstart hk hp
      ⟨j.val + 1, by omega⟩

/-- The initial node pair is exchanged without dropping its positive-start witness. -/
@[reassoc] theorem positiveSplitReflection_initialNode :
    A (.inl (.inl ⟨0, hstart⟩)) ≫ σ = A (.inl (.inl ⟨1, hstart⟩)) := by
  have hEq := positiveSplitReflection_firstNode hπ data D s hs hstart hk hp 0
  change A (b 0 0) ≫ σ = A (b 0 1) at hEq
  simpa only [positiveSplitBranchNode_initial] using hEq

/-- Each original retained node pair is exchanged with no shift of modification depth. -/
@[reassoc] theorem positiveSplitReflection_retainedNode (j : Fin (s + 1)) :
    A (.inl (.inr (j, 0))) ≫ σ = A (.inl (.inr (j, 1))) := by
  simpa only [positiveSplitBranchNode_tail start s hstart ⟨j.val, by omega⟩,
    finalBranchVertex_retained] using
    positiveSplitReflection_firstNode hπ data D s hs hstart hk hp
      ⟨j.val + 1, by omega⟩

end FLT.Mazur.WeierstrassDividedDepth
