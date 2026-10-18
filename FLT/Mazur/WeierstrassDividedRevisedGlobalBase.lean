/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRevisedGlobalIso
public import FLT.Mazur.WeierstrassDividedRevisedInfinityBase
public import FLT.Mazur.WeierstrassDividedRevisedTerminalBase

/-!
# The complete first-order comparison is an isomorphism over the arithmetic base

All original labeled charts have their actual coefficient projection.
Extensionality on that full cover supplies the global base equation.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticRevisedPolygon
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "F" => arithmeticFirstOriginalRevisedGlobalMap hπ data H j hj u hu
local notation "I" => arithmeticFirstOriginalRevisedGlobalIso hπ data H j hj u hu
local notation "B" => arithmeticRevisedPolygonToBase data H 1 j hj u hu
local notation "S" => finiteGlobalArithmeticStructure hπ data (j + 1) hj 1
local notation "a" => arithmeticLabeledAtlasMap hπ data H 1 (j + 1) hj
local notation "G" => arithmeticFirstOriginalRevisedChart hπ data H j hj u hu

/-- Every complete original labeled comparison is over its actual arithmetic quotient. -/
@[reassoc] theorem arithmeticFirstOriginalRevisedChart_base
    (i : ArithmeticChartLabel (j + 1)) : G i ≫ B = a i ≫ S := by
  cases i with
  | infinity =>
    change arithmeticOriginalRevisedTensorInfinityMap data H 1 j hj u hu ≫ B =
      arithmeticTensorAtlasMap hπ data 1 (j + 1) hj 0 ≫ S
    rw [arithmeticOriginalRevisedTensorInfinityMap_base, arithmeticTensorAtlas_infinity_structure]
  | initial b =>
    change arithmeticOriginalRevisedInitialMap data H 1 j hj u hu b ≫ B =
      arithmeticLabeledInitialChart hπ data H 1 (j + 1) hj b ≫ S
    rw [arithmeticOriginalRevisedInitialMap_base, arithmeticLabeledInitialChart_base]
  | retained idx b =>
    change arithmeticFirstOriginalRevisedRetainedMap hπ data H j hj u hu idx b ≫ B =
      arithmeticLabeledRetainedChart hπ data H 1 (j + 1) hj idx b ≫ S
    rw [arithmeticFirstOriginalRevisedRetainedMap_base, arithmeticLabeledRetainedChart_base]
  | terminal => exact arithmeticFirstOriginalRevisedTerminal_base hπ data H j hj u hu

/-- The entire original first-order global comparison preserves its arithmetic base. -/
@[reassoc] theorem arithmeticFirstOriginalRevisedGlobalMap_base : F ≫ B = S := by
  apply arithmeticPositiveLabeled_hom_ext hπ data H 1 j hj
  intro i
  rw [← Category.assoc, arithmeticFirstOriginalRevisedGlobalMap_chart,
    arithmeticFirstOriginalRevisedChart_base]

/-- The inverse complete comparison preserves the same quotient projection. -/
@[reassoc] theorem arithmeticFirstOriginalRevisedGlobalIso_inv_base : (I).inv ≫ S = B := by
  rw [← arithmeticFirstOriginalRevisedGlobalMap_base hπ data H j hj u hu]
  change (I).inv ≫ (I).hom ≫ B = B
  rw [Iso.inv_hom_id_assoc]

/-- The independent revised polygon and the original stage are isomorphic over the base. -/
def arithmeticFirstOriginalRevisedOverIso : Over.mk S ≅ Over.mk B :=
  Over.isoMk I (arithmeticFirstOriginalRevisedGlobalMap_base hπ data H j hj u hu)

end FLT.Mazur.WeierstrassDividedDepth
