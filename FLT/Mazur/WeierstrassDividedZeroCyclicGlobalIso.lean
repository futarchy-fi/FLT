/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCyclicGlobalMap
public import FLT.Mazur.WeierstrassDividedZeroCyclicInverseMap
public import FLT.Mazur.WeierstrassDividedZeroCyclicSourceCover

/-!
# The original depth-zero stage is the independent standard five-gon

The constructed global maps are inverse on both full node covers. The source
retains its common terminal, both original initial opens and exact retained edges.
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
local notation "t" => arithmeticZeroCyclicStandardParameter hπ data H hj u hu m
local notation "G" => arithmeticZeroCyclicGlobalMap hπ data H m hj u hu
local notation "I" => arithmeticZeroCyclicInverseMap hπ data H m hj u hu
local notation "X" => simultaneousTwistedArithmeticStage hπ data H m 0 hj u hu
local notation "Y" => arithmeticZeroCyclicStandard hπ data H hj u hu m

/-- The composed full comparisons fix every point and section of the entire original source. -/
theorem arithmeticZeroCyclicGlobalMap_inverse : G ≫ I = 𝟙 X := by
  apply arithmeticZeroCyclicSourceChart_hom_ext hπ data H m hj u hu
  intro i
  rw [arithmeticZeroCyclicGlobalMap_chart_assoc, Category.comp_id]
  rcases i with _ | (_ | _) | (_ | _) <;>
    simp only [arithmeticZeroCyclicStandardSeedMap, arithmeticZeroCyclicSeedToStandard,
      Category.assoc, arithmeticZeroCyclicInverseMap_chart,
      arithmeticZeroCyclicStandardToSourceNode, Iso.hom_inv_id_assoc] <;> rfl

/-- The opposite composition fixes every complete node of the independent standard target. -/
theorem arithmeticZeroCyclicInverseMap_global : I ≫ G = 𝟙 Y := by
  apply (PolygonVariableSmoothing.chartCover Q 5 t (by decide)).hom_ext
  intro i
  change arithmeticZeroCyclicStandardChart hπ data H hj u hu m i ≫ (I ≫ G) =
    arithmeticZeroCyclicStandardChart hπ data H hj u hu m i ≫ 𝟙 _
  rw [arithmeticZeroCyclicInverseMap_chart_assoc, arithmeticZeroCyclicStandardToSourceNode,
    Category.assoc, arithmeticZeroCyclicGlobalMap_chart,
    arithmeticZeroCyclicStandardSeedMap_index, arithmeticZeroCyclicSeedToStandard,
    Iso.inv_hom_id_assoc, Category.comp_id]

/-- The complete original stage is isomorphic to the independently glued standard five-gon. -/
def arithmeticZeroCyclicGlobalIso : X ≅ Y where
  hom := G
  inv := I
  hom_inv_id := arithmeticZeroCyclicGlobalMap_inverse hπ data H m hj u hu
  inv_hom_id := arithmeticZeroCyclicInverseMap_global hπ data H m hj u hu

/-- The global isomorphism is the constructed entire-node comparison on every source chart. -/
@[reassoc] theorem arithmeticZeroCyclicGlobalIso_chart (i : Fin 5) :
    arithmeticZeroCyclicSourceChart hπ data H m hj u hu (zeroCyclicIndex i) ≫
      (arithmeticZeroCyclicGlobalIso hπ data H m hj u hu).hom =
        (arithmeticZeroCyclicNodeIso hπ data H hj u hu m (zeroCyclicIndex i)).hom ≫
          arithmeticZeroCyclicStandardChart hπ data H hj u hu m i := by
  change _ ≫ G = _
  rw [arithmeticZeroCyclicGlobalMap_chart, arithmeticZeroCyclicStandardSeedMap_index]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
