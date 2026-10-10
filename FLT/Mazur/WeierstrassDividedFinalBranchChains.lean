/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFinalAdjacentOverComponents
public import FLT.Mazur.WeierstrassDividedFinalTerminalOverComponents

/-!
# The two actual projective chains ending at the split terminal node

For each tangent order the adjacent components are followed by its terminal
component. Both endpoints refer to the original fixed node family.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

/-- A chain vertex is its retained node, except for the common terminal vertex. -/
def finalBranchVertex (start s : ℕ) (j : Fin (s + 2)) (i : Fin 2) :
    FinalNodeIndex start s :=
  if h : j.val < s + 1 then .inl (.inr (⟨j.val, h⟩, i)) else .inr ()

/-- Every nonterminal vertex is exactly the original retained node index. -/
theorem finalBranchVertex_retained (start s : ℕ) (j : Fin (s + 1)) (i : Fin 2) :
    finalBranchVertex start s ⟨j.val, by omega⟩ i = .inl (.inr (j, i)) := by
  simp only [finalBranchVertex, dite_eq_left j.isLt]

/-- Both chains end at the same terminal index. -/
theorem finalBranchVertex_terminal (start s : ℕ) (i : Fin 2) :
    finalBranchVertex start s ⟨s + 1, by omega⟩ i = .inr () := by
  simp only [finalBranchVertex, lt_self_iff_false, dite_false]

variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "p" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  (finiteGlobalStructure hπ data (s + 1) hs)

/-- A complete original chain, including its final projective component. -/
def finalBranchComponent (j : Fin (s + 1)) (i : Fin 2) :
    PolygonPinching.component K ⟶ Over.mk p :=
  if h : j.val < s then finalAdjacentOverComponent hπ data D s hs hk ⟨j.val, h⟩ i
  else finalTerminalOverComponent hπ data D s hs hk hp i

/-- The retained part consists of the entire original adjacent components. -/
theorem finalBranchComponent_adjacent (j : Fin s) (i : Fin 2) :
    finalBranchComponent hπ data D s hs hk hp ⟨j.val, by omega⟩ i =
      finalAdjacentOverComponent hπ data D s hs hk j i := by
  simp only [finalBranchComponent, dite_eq_left j.isLt]

/-- The last edge is the entire original terminal component. -/
theorem finalBranchComponent_terminal (i : Fin 2) :
    finalBranchComponent hπ data D s hs hk hp ⟨s, by omega⟩ i =
      finalTerminalOverComponent hπ data D s hs hk hp i := by
  simp only [finalBranchComponent, lt_self_iff_false, dite_false]

/-- Every chain edge starts at its original retained node. -/
@[reassoc] theorem finalBranchComponent_zero (j : Fin (s + 1)) (i : Fin 2) :
    ProjectiveLine.zeroSection K ≫ finalBranchComponent hπ data D s hs hk hp j i =
      finalNodeOverSection hπ data D s hs hk hp
        (finalBranchVertex start s ⟨j.val, by omega⟩ i) := by
  rw [finalBranchVertex_retained]
  by_cases h : j.val < s
  · rw [finalBranchComponent, dite_eq_left h, finalAdjacentOverComponent_zero]
  · have hj : j = ⟨s, Nat.lt_succ_self s⟩ := Fin.ext (show j.val = s by omega)
    subst j
    rw [finalBranchComponent_terminal, finalTerminalOverComponent_zero]

/-- Every chain edge ends at the next vertex, including the terminal node. -/
@[reassoc] theorem finalBranchComponent_infinity (j : Fin (s + 1)) (i : Fin 2) :
    ProjectiveLine.infinitySection K ≫ finalBranchComponent hπ data D s hs hk hp j i =
      finalNodeOverSection hπ data D s hs hk hp
        (finalBranchVertex start s ⟨j.val + 1, by omega⟩ i) := by
  by_cases h : j.val < s
  · rw [finalBranchComponent, dite_eq_left h, finalAdjacentOverComponent_infinity,
      finalBranchVertex, dite_eq_left (show j.val + 1 < s + 1 by omega)]
  · have hj : j = ⟨s, Nat.lt_succ_self s⟩ := Fin.ext (show j.val = s by omega)
    subst j
    rw [finalBranchComponent_terminal, finalTerminalOverComponent_infinity,
      finalBranchVertex_terminal]

/-- Consecutive complete components meet at the very same original retained section. -/
theorem finalBranchComponent_consecutive (j : Fin s) (i : Fin 2) :
    ProjectiveLine.infinitySection K ≫
        finalBranchComponent hπ data D s hs hk hp ⟨j.val, by omega⟩ i =
      ProjectiveLine.zeroSection K ≫
        finalBranchComponent hπ data D s hs hk hp ⟨j.val + 1, by omega⟩ i := by
  rw [finalBranchComponent_infinity, finalBranchComponent_zero]

end FLT.Mazur.WeierstrassDividedDepth
