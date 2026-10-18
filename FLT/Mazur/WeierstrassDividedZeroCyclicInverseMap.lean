/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCyclicSourceEdges
public import FLT.Mazur.WeierstrassDividedZeroCyclicStandard

/-!
# The independent standard five-gon maps back to the original stage

The inverse full-node comparisons respect all five standard reciprocal edges.
Descent uses the independent standard polygon's universal property.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "S" => arithmeticZeroCyclicSeed hπ data H hj u hu
local notation "D" => arithmeticZeroCyclicDiagonal hπ data H hj u hu
local notation "N" => arithmeticZeroCyclicNodeIso hπ data H hj u hu m
local notation "P" => arithmeticZeroCyclicPunctureIso hπ data H hj u hu m
local notation "f" => arithmeticZeroCyclicSourceChart hπ data H m hj u hu
local notation "t" => arithmeticZeroCyclicStandardParameter hπ data H hj u hu m
local notation "X" => simultaneousTwistedArithmeticStage hπ data H m 0 hj u hu

/-- The inverse entire node comparison retains each full seed puncture. -/
@[reassoc] theorem arithmeticZeroCyclicNodeIso_inv_puncture (i : ZeroCyclicVertex) (b : Bool) :
    (P i b).hom ≫ punctureOpen ((D).parameter m i) b ≫ (N i).inv =
      punctureOpen ((S).parameter m i) b := by
  rw [← Category.assoc, ← arithmeticZeroCyclicNodeIso_puncture,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Each entire standard node maps back through its actual full-node inverse. -/
def arithmeticZeroCyclicStandardToSourceNode (i : Fin 5) :
    PolygonSmoothing.chart Q (t i) ⟶ X := (N (zeroCyclicIndex i)).inv ≫ f (zeroCyclicIndex i)

local notation "g" => arithmeticZeroCyclicStandardToSourceNode hπ data H m hj u hu

/-- The inverse full-node maps respect every standard reciprocal edge. -/
@[reassoc] theorem arithmeticZeroCyclicStandardToSourceNode_edge (i : Fin 5) :
    leftBranchOpen Q (t i) ≫ g i =
      precedingBranch Q (t ((finRotate 5).symm i)) ≫ g ((finRotate 5).symm i) := by
  apply (cancel_epi (P (zeroCyclicIndex i) true).hom).mp
  simp only [arithmeticZeroCyclicStandardToSourceNode, precedingBranch, Category.assoc]
  change (P (zeroCyclicIndex i) true).hom ≫
    leftBranchOpen Q ((D).parameter m (zeroCyclicIndex i)) ≫ _ = _
  rw [← punctureOpen_true, arithmeticZeroCyclicNodeIso_inv_puncture_assoc,
    punctureOpen_true, arithmeticZeroCyclicSourceChart_edge,
    arithmeticZeroCyclicPunctureIso_edge_assoc]
  have he := congrArg (fun j ↦ (P j false).hom) (zeroCyclicIndex_preceding i)
  rw [← he]
  simp only [arithmeticZeroCyclicStandardParameter, ← punctureOpen_false,
    arithmeticZeroCyclicNodeIso_inv_puncture_assoc]
  exact congrArg ((punctureSpecIso ((S).edge m (zeroCyclicIndex i))).hom ≫ ·)
    (congrArg (fun j ↦ punctureOpen ((S).parameter m j) false ≫ f j)
      (zeroCyclicIndex_preceding i)).symm

/-- Descend the inverse full-node maps from the independent standard target. -/
def arithmeticZeroCyclicInverseMap :
    arithmeticZeroCyclicStandard hπ data H hj u hu m ⟶ X :=
  PolygonVariableSmoothing.desc Q 5 t (by decide) g
    (arithmeticZeroCyclicStandardToSourceNode_edge hπ data H m hj u hu)

/-- The descended inverse retains every complete standard node map. -/
@[reassoc] theorem arithmeticZeroCyclicInverseMap_chart (i : Fin 5) :
    arithmeticZeroCyclicStandardChart hπ data H hj u hu m i ≫
      arithmeticZeroCyclicInverseMap hπ data H m hj u hu = g i :=
  PolygonVariableSmoothing.chart_desc Q 5 t (by decide) g
    (arithmeticZeroCyclicStandardToSourceNode_edge hπ data H m hj u hu) i

end FLT.Mazur.WeierstrassDividedDepth
