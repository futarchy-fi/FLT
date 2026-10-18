/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRevisedLabeledMaps
public import FLT.Mazur.WeierstrassDividedArithmeticPositiveLabeledDescent

/-!
# The complete original first-order model maps to the independent revised polygon

All original full overlap equations are proved for the concrete chart family.
Descent gives the global comparison with every original labeled restriction.
This constructs a morphism; global invertibility is a separate geometric step.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticOriginalRevisedTensorInfinityMap arithmeticOriginalRevisedInitialMap
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "F" => arithmeticFirstOriginalRevisedChart hπ data H j hj u hu
local notation "c" => arithmeticLabeledAtlasMap hπ data H 1 (j + 1) hj

/-- Both full original infinity overlaps commute for the concrete complete chart family. -/
theorem arithmeticFirstOriginalRevisedChart_infinity :
    arithmeticInitialInfinityCompatible hπ data H 1 (j + 1) hj F := by
  have hf : arithmeticInitialOverlapToInfinity hπ data 1 (j + 1) hj
      H.a1_unit H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _) ≫ F .infinity =
        polynomialNodeOverlapInclusion (W.map (algebraMap R (Quotient R π 1)))
          (algebraMap R (Quotient R π 1) (π ^ 1)) ≫ F (.initial false) := by
    rw [← arithmeticFactorRatioOverlapInfinity_eq_atlas hπ data H 1 (j + 1) hj]
    exact arithmeticOriginalRevisedTensorInfinityMap_overlap data H 1 j hj u hu
  constructor
  · exact hf
  · rw [hf]
    exact arithmeticOriginalRevisedInitialMap_overlap data H 1 j hj u hu

/-- Every full original labeled fiber product satisfies the descent equation. -/
theorem arithmeticFirstOriginalRevisedChart_compatible (a b : ArithmeticChartLabel (j + 1)) :
    pullback.fst (c a) (c b) ≫ F a = pullback.snd (c a) (c b) ≫ F b :=
  arithmeticPositiveLabeled_compatible hπ data H 1 j hj F
    (arithmeticFirstOriginalRevisedChart_infinity hπ data H j hj u hu)
    (arithmeticFirstOriginalRevisedChart_initial hπ data H j hj u hu)
    (arithmeticFirstOriginalRevisedChart_adjacent hπ data H j hj u hu)
    (arithmeticFirstOriginalRevisedChart_terminal hπ data H j hj u hu) a b

/-- The actual complete original first-order model maps into the independently glued target. -/
def arithmeticFirstOriginalRevisedGlobalMap :
    finiteGlobalArithmeticStage hπ data (j + 1) hj 1 ⟶
      arithmeticRevisedPolygon data H 1 j hj u hu :=
  arithmeticPositiveLabeledDesc hπ data H 1 j hj F
    (arithmeticFirstOriginalRevisedChart_infinity hπ data H j hj u hu)
    (arithmeticFirstOriginalRevisedChart_initial hπ data H j hj u hu)
    (arithmeticFirstOriginalRevisedChart_adjacent hπ data H j hj u hu)
    (arithmeticFirstOriginalRevisedChart_terminal hπ data H j hj u hu)

/-- The global comparison recovers every full original labeled chart map. -/
@[reassoc] theorem arithmeticFirstOriginalRevisedGlobalMap_chart
    (i : ArithmeticChartLabel (j + 1)) :
    c i ≫ arithmeticFirstOriginalRevisedGlobalMap hπ data H j hj u hu = F i :=
  arithmeticPositiveLabeledDesc_chart hπ data H 1 j hj F _ _ _ _ i

/-- These concrete full chart formulas uniquely determine the global comparison. -/
theorem arithmeticFirstOriginalRevisedGlobalMap_unique
    (g : finiteGlobalArithmeticStage hπ data (j + 1) hj 1 ⟶
      arithmeticRevisedPolygon data H 1 j hj u hu) (hg : ∀ i, c i ≫ g = F i) :
    g = arithmeticFirstOriginalRevisedGlobalMap hπ data H j hj u hu := by
  apply arithmeticPositiveLabeled_hom_ext hπ data H 1 j hj
  intro i
  rw [hg i, arithmeticFirstOriginalRevisedGlobalMap_chart]

end FLT.Mazur.WeierstrassDividedDepth
