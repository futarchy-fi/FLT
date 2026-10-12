/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityReflection
public import FLT.Mazur.CyclicPinchingReflectionIndices

/-!
# Reflection on the original complete branches and attachments

Resolve cyclic reflection into the original geometric components. Both
chains keep their level and parameter; the exterior and terminal reverse.
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
  (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "p" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  (finiteGlobalStructure hπ data (s + 1) hs)
local notation "Z" => positiveEqualityCycleComponent hπ data D s hs hstart hk hp
local notation "N" => positiveEqualityCycleNormalization hπ data D s hs hstart hk hp
local notation "Q" => positiveEqualityCycleNodes hπ data D s hs hstart hk
local notation "H" => positiveEqualityCycleCocone_isPushout hπ data D s hs hstart hk hp
local notation "ρ" => Iso.hom (ProjectiveLine.endpointReversalOverIso K)

local notation "σ" => positiveEqualityReflection hπ data D s hs hstart hk hp
local notation "C" => positiveEqualityBranchComponent hπ data D s hs hstart hk
local notation "A" => equalityNodeOverSection hπ data D s hs hk
local notation "b" => positiveEqualityBranchNode start s hstart

/-- The complete exterior is fixed with its projective coordinate reversed. -/
@[reassoc] theorem positiveEqualityReflection_exterior :
    equalityInitialExteriorOverComponent hπ data D s hs hstart hk ≫ σ =
      ρ ≫ equalityInitialExteriorOverComponent hπ data D s hs hstart hk := by
  have hEq := positiveEqualityReflection_component hπ data D s hs hstart hk hp 0
  simpa only [PolygonPinching.reflectIndex_zero, positiveEqualityCycleComponent_exterior] using hEq

/-- The full first branch goes to the second at the same level and with the same parameter. -/
@[reassoc] theorem positiveEqualityReflection_firstBranch (j : Fin (s + 1)) :
    C j 0 ≫ σ = C j 1 := by
  have hEq := positiveEqualityReflection_component hπ data D s hs hstart hk hp
    ⟨j.val + 1, by omega⟩
  rw [PolygonPinching.reflectIndex_firstChain, positiveEqualityCycleComponent_first,
    positiveEqualityCycleComponent_second, Category.assoc] at hEq
  exact (cancel_epi ρ).mp hEq

/-- The opposite complete branch returns with its original parameter unchanged. -/
@[reassoc] theorem positiveEqualityReflection_secondBranch (j : Fin (s + 1)) :
    C j 1 ≫ σ = C j 0 := by
  rw [← positiveEqualityReflection_firstBranch hπ data D s hs hstart hk hp j,
    Category.assoc, positiveEqualityReflection_involutive, Category.comp_id]

/-- The single complete terminal component is fixed with its endpoints reversed. -/
@[reassoc] theorem positiveEqualityReflection_terminal :
    equalityTerminalOverComponent hπ data D s hs hk hp ≫ σ =
      ρ ≫ equalityTerminalOverComponent hπ data D s hs hk hp := by
  have hEq := positiveEqualityReflection_component hπ data D s hs hstart hk hp
    ⟨s + 2, by omega⟩
  rw [PolygonPinching.reflectIndex_terminal, positiveEqualityCycleComponent_terminal,
    Category.assoc] at hEq
  exact (cancel_epi ρ).mp hEq

/-- First-branch attachments go to the corresponding original second-branch sections. -/
@[reassoc] theorem positiveEqualityReflection_firstNode (j : Fin (s + 2)) :
    A (b j 0) ≫ σ = A (b j 1) := by
  have hEq := positiveEqualityReflection_node hπ data D s hs hstart hk hp
    ⟨j.val, by omega⟩
  simpa only [PolygonPinching.reflectNodeIndex_firstChain, positiveEqualityCycleNodeIndex_first,
    positiveEqualityCycleNodeIndex_second] using hEq

/-- Every opposite attachment returns to its partner, including the terminal pair. -/
@[reassoc] theorem positiveEqualityReflection_secondNode (j : Fin (s + 2)) :
    A (b j 1) ≫ σ = A (b j 0) := by
  rw [← positiveEqualityReflection_firstNode hπ data D s hs hstart hk hp j,
    Category.assoc, positiveEqualityReflection_involutive, Category.comp_id]

/-- Both original initial projective components are exchanged as entire schemes. -/
@[reassoc] theorem positiveEqualityReflection_initial :
    equalityInitialOverComponent hπ data D s hs hstart hk 0 ≫ σ =
      equalityInitialOverComponent hπ data D s hs hstart hk 1 := by
  simpa only [positiveEqualityBranchComponent_initial] using
    positiveEqualityReflection_firstBranch hπ data D s hs hstart hk hp 0

/-- Every retained adjacent projective component is exchanged at its actual level. -/
@[reassoc] theorem positiveEqualityReflection_adjacent (j : Fin s) :
    finalAdjacentOverComponent hπ data D s hs hk j 0 ≫ σ =
      finalAdjacentOverComponent hπ data D s hs hk j 1 := by
  simpa only [positiveEqualityBranchComponent_adjacent] using
    positiveEqualityReflection_firstBranch hπ data D s hs hstart hk hp
      ⟨j.val + 1, by omega⟩

/-- The initial node pair is exchanged without dropping its positive-start witness. -/
@[reassoc] theorem positiveEqualityReflection_initialNode :
    A (.inl ⟨0, hstart⟩) ≫ σ = A (.inl ⟨1, hstart⟩) := by
  simpa only [positiveEqualityBranchNode_initial] using
    positiveEqualityReflection_firstNode hπ data D s hs hstart hk hp 0

/-- Each original retained node pair is exchanged with no shift of modification depth. -/
@[reassoc] theorem positiveEqualityReflection_retainedNode (j : Fin (s + 1)) :
    A (.inr (j, 0)) ≫ σ = A (.inr (j, 1)) := by
  simpa only [positiveEqualityBranchNode_retained] using
    positiveEqualityReflection_firstNode hπ data D s hs hstart hk hp
      ⟨j.val + 1, by omega⟩

end FLT.Mazur.WeierstrassDividedDepth
