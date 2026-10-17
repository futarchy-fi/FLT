/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroFirstGeometry
public import FLT.Mazur.WeierstrassDividedFourthZeroResidual

/-!
# Install the complete first depth-zero correction atlas

The original initial open and the unique last node receive the two full first
factors. The existing common terminal is retained, including its full smoothing.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthOuterAtlasChart arithmeticZeroFirstInitialIso arithmeticZeroFirstLastIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "B" => arithmeticFourthOuterAtlasObject hπ data H m 0 hj u hu
local notation "κ" => arithmeticFourthOuterAtlasChart hπ data H m 0 hj u hu
local notation "I" => arithmeticFourthOuterAtlasIso hπ data H m 0 hj u hu

/-- The first objects at each actual depth-zero label, including the original infinity. -/
def arithmeticZeroFirstAtlasObject : ArithmeticChartLabel 1 → Scheme
  | .initial b => arithmeticZeroFirstInitialObject hπ data H m 0 hj u hu b
  | .retained _ b => PolygonSmoothing.chart Q
      (arithmeticZeroFirstLastSmoothing hπ data H 0 hj u hu m b)
  | .terminal => B .terminal
  | .infinity => B .infinity

local notation "A" => arithmeticZeroFirstAtlasObject hπ data H m hj u hu

/-- All first factors are installed together from the same fourth atlas. -/
def arithmeticZeroFirstAtlasCorrection (i : ArithmeticChartLabel 1) : B i ≅ A i :=
  match i with
  | .initial b =>
    (arithmeticFourthOuterInitialZeroIdentification hπ data H m 0 hj u hu rfl b).symm ≪≫
      arithmeticZeroFirstInitialIso hπ data H m 0 hj u hu b
  | .retained ⟨0, _⟩ b =>
    (arithmeticFourthOuterLastIdentification hπ data H m 0 hj u hu b).symm ≪≫
      (twistedRetainedOrientation data H m b).symm ≪≫
        arithmeticZeroFirstLastIso hπ data H m 0 hj u hu b
  | .retained ⟨k + 1, hk⟩ _ => False.elim (by omega)
  | .terminal => Iso.refl _
  | .infinity => Iso.refl _

attribute [local irreducible] arithmeticZeroFirstAtlasCorrection
local notation "E" => arithmeticZeroFirstAtlasCorrection hπ data H m hj u hu

/-- The full first chart inclusion in the unchanged global target. -/
def arithmeticZeroFirstAtlasChart (i : ArithmeticChartLabel 1) :
    A i ⟶ simultaneousTwistedArithmeticStage hπ data H m 0 hj u hu :=
  (E i).inv ≫ κ i

instance arithmeticZeroFirstAtlasChart_isOpenImmersion (i : ArithmeticChartLabel 1) :
    IsOpenImmersion (arithmeticZeroFirstAtlasChart hπ data H m hj u hu i) := by
  unfold arithmeticZeroFirstAtlasChart
  infer_instance

/-- The comparison from each original chart includes all accumulated complete correction rounds. -/
def arithmeticZeroFirstAtlasIso (i : ArithmeticChartLabel 1) :
    arithmeticLabeledAtlasObject hπ data H m 1 hj i ≅ A i := I i ≪≫ E i

local notation "ι" => arithmeticZeroFirstAtlasChart hπ data H m hj u hu

/-- The installed correction recovers the exact fourth inclusion at every label. -/
@[reassoc] theorem arithmeticZeroFirstAtlasCorrection_chart (i : ArithmeticChartLabel 1) :
    (E i).hom ≫ ι i = κ i := by
  rw [arithmeticZeroFirstAtlasChart, Iso.hom_inv_id_assoc]

/-- The original global inclusion is recovered by the composed full chart comparison. -/
@[reassoc] theorem arithmeticZeroFirstAtlasIso_chart (i : ArithmeticChartLabel 1) :
    arithmeticLabeledAtlasMap hπ data H m 1 hj i ≫
        (simultaneousTwistedArithmeticIso hπ data H m 0 hj u hu).hom =
      (arithmeticZeroFirstAtlasIso hπ data H m hj u hu i).hom ≫ ι i := by
  rw [arithmeticZeroFirstAtlasIso, Iso.trans_hom, Category.assoc,
    arithmeticZeroFirstAtlasCorrection_chart]
  exact arithmeticFourthOuterAtlasIso_chart hπ data H m 0 hj u hu i

attribute [local irreducible] arithmeticZeroFirstAtlasChart

/-- The simultaneous first factors transport the entire original cover. -/
def arithmeticZeroFirstOpenCover :
    (simultaneousTwistedArithmeticStage hπ data H m 0 hj u hu).OpenCover :=
  (arithmeticFourthOuterOpenCover hπ data H m 0 hj u hu).copy
    (ArithmeticChartLabel 1) A ι (Equiv.refl _) (fun i ↦ (E i).symm)
      (fun _ ↦ by rw [arithmeticZeroFirstAtlasChart]; rfl)

/-- Every point of the full global target remains covered by a first chart. -/
theorem arithmeticZeroFirstAtlas_cover
    (z : simultaneousTwistedArithmeticStage hπ data H m 0 hj u hu) :
    ∃ i x, ι i x = z := (arithmeticZeroFirstOpenCover hπ data H m hj u hu).exists_eq z

end FLT.Mazur.WeierstrassDividedDepth
