/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCyclicStandard

/-!
# The complete seed nodes map compatibly into the independent standard target

All five whole-node maps retain both punctures. Their exact original Laurent
edges agree globally after the constructed simultaneous node comparisons.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "S" => arithmeticZeroCyclicSeed hπ data H hj u hu
local notation "D" => arithmeticZeroCyclicDiagonal hπ data H hj u hu
local notation "Q" => fun m ↦ Quotient R π m
local notation "c" => arithmeticZeroCyclicStandardChart hπ data H hj u hu
local notation "N" => arithmeticZeroCyclicNodeIso hπ data H hj u hu
local notation "P" => arithmeticZeroCyclicPunctureIso hπ data H hj u hu
local notation "e" => zeroCyclicIndex

/-- Each entire seed node enters the independently glued standard target. -/
def arithmeticZeroCyclicSeedToStandard (m : ℕ) (i : Fin 5) :
    PolygonSmoothing.chart (Q m) ((S).parameter m (e i)) ⟶
      arithmeticZeroCyclicStandard hπ data H hj u hu m :=
  (N m (e i)).hom ≫ c m i

local notation "f" => arithmeticZeroCyclicSeedToStandard hπ data H hj u hu

instance arithmeticZeroCyclicSeedToStandard_isOpenImmersion (m : ℕ) (i : Fin 5) :
    IsOpenImmersion (f m i) := by
  unfold arithmeticZeroCyclicSeedToStandard
  infer_instance

/-- Both full seed punctures follow the same entire node into the standard target. -/
@[reassoc] theorem arithmeticZeroCyclicSeedToStandard_puncture
    (m : ℕ) (i : Fin 5) (a : Bool) :
    punctureOpen ((S).parameter m (e i)) a ≫ f m i =
      (P m (e i) a).hom ≫ punctureOpen ((D).parameter m (e i)) a ≫ c m i := by
  rw [arithmeticZeroCyclicSeedToStandard, ← Category.assoc,
    arithmeticZeroCyclicNodeIso_puncture, Category.assoc]

/-- Every full original cyclic edge agrees in the independently constructed standard target. -/
@[reassoc] theorem arithmeticZeroCyclicSeedToStandard_edge (m : ℕ) (i : Fin 5) :
    leftBranchOpen (Q m) ((S).parameter m (e i)) ≫ f m i =
      (punctureSpecIso ((S).edge m (e i))).hom ≫
        rightBranchOpen (Q m) ((S).parameter m (e ((finRotate 5).symm i))) ≫
          f m ((finRotate 5).symm i) := by
  have ht := arithmeticZeroCyclicSeedToStandard_puncture hπ data H hj u hu m i true
  have hf := arithmeticZeroCyclicSeedToStandard_puncture hπ data H hj u hu m
    ((finRotate 5).symm i) false
  rw [punctureOpen_true, punctureOpen_true] at ht
  rw [punctureOpen_false, punctureOpen_false] at hf
  rw [ht, hf]
  change (P m (e i) true).hom ≫
    leftBranchOpen (Q m) (arithmeticZeroCyclicStandardParameter hπ data H hj u hu m i) ≫ _ = _
  rw [arithmeticZeroCyclicStandard_overlap, precedingBranch]
  simp only [Category.assoc, arithmeticZeroCyclicStandardParameter]
  have he := congrArg (fun j ↦ (P m j false).hom) (zeroCyclicIndex_preceding i)
  rw [arithmeticZeroCyclicPunctureIso_edge_assoc, he]

end FLT.Mazur.WeierstrassDividedDepth
