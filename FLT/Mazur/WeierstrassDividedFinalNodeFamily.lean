/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOrderedRetainedSections
public import FLT.Mazur.WeierstrassDividedInitialGlobalSections
public import FLT.Mazur.WeierstrassDividedTerminalBranchesNodeIntersection

/-!
# Original node sections in one fixed final-stage family

Only equality of natural-number stage indices is used for transport. The initial
ordered nodes are present precisely when their positive-depth construction applies.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

/-- Initial ordered nodes, all retained ordered pairs, and the terminal node. -/
abbrev FinalNodeIndex (start s : ℕ) :=
  ({_i : Fin 2 // 0 < start} ⊕ (Fin (s + 1) × Fin 2)) ⊕ Unit

variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth)
local notation "K" => ResidueField R

/-- A retained section with its target index written as a fixed stage. -/
def retainedNodeSectionAt (t : ℕ) (ht : t ≤ n) (j : ℕ) (hj : j + 1 ≤ t)
    (hk : 2 * (start + j + 1) ≤ depth) (i : Fin 2) :
    Spec (.of K) ⟶ finiteGlobalTensorModel hπ data K t ht :=
  orderedRetainedSection hπ data D j (by omega) (t - (j + 1)) (by omega) hk i ≫
    eqToHom (finiteGlobalTensorModel_index_congr hπ data K (by omega) ht (by omega))

/-- Returning to the original stage expression recovers the entire original map. -/
theorem retainedNodeSectionAt_original (j : ℕ) (hj : j + 1 ≤ n)
    (r : ℕ) (hr : j + 1 + r ≤ n) (hk : 2 * (start + j + 1) ≤ depth) (i : Fin 2) :
    retainedNodeSectionAt hπ data D (j + 1 + r) hr j (by omega) hk i =
      orderedRetainedSection hπ data D j hj r hr hk i := by
  apply eq_of_heq
  refine (comp_eqToHom_heq _ _).trans ?_
  congr 1
  · omega
  · apply proof_irrel_heq

/-- The target transport preserves the ordered distinction at every retained stage. -/
theorem retainedNodeSectionAt_ne (t : ℕ) (ht : t ≤ n) (j : ℕ) (hj : j + 1 ≤ t)
    (hk : 2 * (start + j + 1) ≤ depth) :
    retainedNodeSectionAt hπ data D t ht j hj hk 0 ≠
      retainedNodeSectionAt hπ data D t ht j hj hk 1 := by
  intro h
  exact orderedRetainedSection_ne hπ data D j (by omega) (t - (j + 1)) (by omega) hk
    ((cancel_mono _).mp h)

variable (s : ℕ) (hs : s + 1 ≤ n)
  (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) < depth)

/-- The fixed family contains the actual maps, with no distinctness hypotheses. -/
def finalNodeSection (i : FinalNodeIndex start s) :
    Spec (.of K) ⟶ finiteGlobalTensorModel hπ data K (s + 1) hs :=
  match i with
  | .inl (.inl a) =>
    Fin.cases (initialGlobalFirstSection hπ data D (s + 1) hs a.property (by omega))
      (fun _ => initialGlobalSecondSection hπ data D (s + 1) hs a.property (by omega))
      a.val
  | .inl (.inr a) =>
    retainedNodeSectionAt hπ data D (s + 1) hs a.1.val (by omega) (by omega) a.2
  | .inr _ => terminalConicNodeSection hπ data D s hs hk hp

/-- The first complete terminal branch still has precisely the family's terminal origin. -/
@[reassoc] theorem finalNodeSection_firstBranch_origin :
    ProjectiveLine.chartZero K ≫ terminalConicFirstBranch hπ data D s hs hk hp =
      finalNodeSection hπ data D s hs hk hp (.inr ()) :=
  terminalConicFirstBranch_origin hπ data D s hs hk hp

/-- The other complete terminal branch has that same original terminal origin. -/
@[reassoc] theorem finalNodeSection_secondBranch_origin :
    ProjectiveLine.chartZero K ≫ terminalConicSecondBranch hπ data D s hs hk hp =
      finalNodeSection hπ data D s hs hk hp (.inr ()) :=
  terminalConicSecondBranch_origin hπ data D s hs hk hp

/-- Each retained ordered pair remains distinct inside the fixed family. -/
theorem finalNodeSection_retained_ne (j : Fin (s + 1)) :
    finalNodeSection hπ data D s hs hk hp (.inl (.inr (j, 0))) ≠
      finalNodeSection hπ data D s hs hk hp (.inl (.inr (j, 1))) :=
  retainedNodeSectionAt_ne hπ data D (s + 1) hs j.val (by omega) (by omega)

/-- The initial ordered pair retains its distinction inside the same family. -/
theorem finalNodeSection_initial_ne (hstart : 0 < start) :
    finalNodeSection hπ data D s hs hk hp (.inl (.inl ⟨0, hstart⟩)) ≠
      finalNodeSection hπ data D s hs hk hp (.inl (.inl ⟨1, hstart⟩)) :=
  initialGlobalSections_ne hπ data D (s + 1) hs hstart (by omega)

end FLT.Mazur.WeierstrassDividedDepth
