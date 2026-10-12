/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootFinalAdjacent
public import FLT.Mazur.WeierstrassCoefficientShearRootFinalTerminal
public import FLT.Mazur.WeierstrassCoefficientShearGluedOverIso
public import FLT.Mazur.WeierstrassDividedFinalBranchChains

/-!
# Independent complete branch chains in the coefficient model

Join the independently constructed adjacent and terminal components using
the original final vertices. The reconstruction compares the whole chains.
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
  (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "p" => coefficientShearGluedStructure hπ data K 0 (s + 1) hs
local notation "E" => coefficientShearGluedOverIso hπ data K 0 (s + 1) hs

/-- The original indexed node section in the coefficient model. -/
def coefficientShearFinalNodeOverSection (a : FinalNodeIndex start s) :
    Over.mk (𝟙 (Spec (.of K))) ⟶ Over.mk p :=
  finalNodeOverSection hπ data D s hs hk hp a ≫ (E).inv

/-- Reconstruction retains the actual node, with the original index unchanged. -/
@[reassoc] theorem coefficientShearFinalNodeOverSection_original (a : FinalNodeIndex start s) :
    coefficientShearFinalNodeOverSection hπ data D s hs hk hp a ≫ (E).hom =
      finalNodeOverSection hπ data D s hs hk hp a := by
  rw [coefficientShearFinalNodeOverSection, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Each independent retained pair reconstructs the original pair over the residue field. -/
@[reassoc] theorem coefficientShearRootFinalAdjacentOverComponent_original
    (j : Fin s) (i : Fin 2) :
    coefficientShearRootFinalAdjacentOverComponent hπ data D s hs hk j i ≫ (E).hom =
      finalAdjacentOverComponent hπ data D s hs hk j i := by
  apply Over.OverMorphism.ext
  exact coefficientShearRootFinalAdjacentComponent_original hπ data D s hs hk j i

/-- The independent terminal pair reconstructs both original full over-components. -/
@[reassoc] theorem coefficientShearRootFinalTerminalOverComponent_original (i : Fin 2) :
    coefficientShearRootFinalTerminalOverComponent hπ data D s hs hk hp i ≫ (E).hom =
      finalTerminalOverComponent hπ data D s hs hk hp i := by
  apply Over.OverMorphism.ext
  exact coefficientShearRootFinalTerminalComponent_original hπ data D s hs hk hp i

/-- Each complete independent chain includes its actual last terminal component. -/
def coefficientShearRootFinalBranchComponent (j : Fin (s + 1)) (i : Fin 2) :
    PolygonPinching.component K ⟶ Over.mk p :=
  if h : j.val < s then
    coefficientShearRootFinalAdjacentOverComponent hπ data D s hs hk ⟨j.val, h⟩ i
  else coefficientShearRootFinalTerminalOverComponent hπ data D s hs hk hp i

/-- Reconstruction preserves every component at its original level in the original chain. -/
@[reassoc] theorem coefficientShearRootFinalBranchComponent_original
    (j : Fin (s + 1)) (i : Fin 2) :
    coefficientShearRootFinalBranchComponent hπ data D s hs hk hp j i ≫ (E).hom =
      finalBranchComponent hπ data D s hs hk hp j i := by
  unfold coefficientShearRootFinalBranchComponent finalBranchComponent
  split_ifs
  · exact coefficientShearRootFinalAdjacentOverComponent_original hπ data D s hs hk _ i
  · exact coefficientShearRootFinalTerminalOverComponent_original hπ data D s hs hk hp i

/-- The zero marking is the original branch vertex, including the first retained level. -/
@[reassoc] theorem coefficientShearRootFinalBranchComponent_zero
    (j : Fin (s + 1)) (i : Fin 2) :
    ProjectiveLine.zeroSection K ≫
        coefficientShearRootFinalBranchComponent hπ data D s hs hk hp j i =
      coefficientShearFinalNodeOverSection hπ data D s hs hk hp
        (finalBranchVertex start s ⟨j.val, by omega⟩ i) := by
  apply (cancel_mono (E).hom).mp
  rw [Category.assoc, coefficientShearRootFinalBranchComponent_original,
    coefficientShearFinalNodeOverSection_original, finalBranchComponent_zero]

/-- The infinity marking is the next original vertex, including the common terminal vertex. -/
@[reassoc] theorem coefficientShearRootFinalBranchComponent_infinity
    (j : Fin (s + 1)) (i : Fin 2) :
    ProjectiveLine.infinitySection K ≫
        coefficientShearRootFinalBranchComponent hπ data D s hs hk hp j i =
      coefficientShearFinalNodeOverSection hπ data D s hs hk hp
        (finalBranchVertex start s ⟨j.val + 1, by omega⟩ i) := by
  apply (cancel_mono (E).hom).mp
  rw [Category.assoc, coefficientShearRootFinalBranchComponent_original,
    coefficientShearFinalNodeOverSection_original, finalBranchComponent_infinity]

/-- Consecutive independently glued complete components share the same original node map. -/
theorem coefficientShearRootFinalBranchComponent_consecutive (j : Fin s) (i : Fin 2) :
    ProjectiveLine.infinitySection K ≫
        coefficientShearRootFinalBranchComponent hπ data D s hs hk hp ⟨j.val, by omega⟩ i =
      ProjectiveLine.zeroSection K ≫
        coefficientShearRootFinalBranchComponent hπ data D s hs hk hp ⟨j.val + 1, by omega⟩ i := by
  rw [coefficientShearRootFinalBranchComponent_infinity,
    coefficientShearRootFinalBranchComponent_zero]

end FLT.Mazur.WeierstrassDividedDepth
