/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroThirdGeometry
public import FLT.Mazur.WeierstrassDividedZeroSecondAtlas

/-!
# Install the complete third depth-zero correction atlas

The original initial open and the unique last node receive the two full third
factors. The same common terminal receives both closing corrections on its full second smoothing.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroSecondAtlasChart arithmeticZeroThirdInitialIso arithmeticZeroThirdLastIso
  arithmeticZeroThirdTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "B" => arithmeticZeroSecondAtlasObject hπ data H m hj u hu
local notation "κ" => arithmeticZeroSecondAtlasChart hπ data H m hj u hu
local notation "I" => arithmeticZeroSecondAtlasIso hπ data H m hj u hu

/-- The third objects at each actual depth-zero label, including the original infinity. -/
def arithmeticZeroThirdAtlasObject : ArithmeticChartLabel 1 → Scheme
  | .initial b => arithmeticZeroThirdInitialObject hπ data H m 0 hj u hu b
  | .retained _ b => PolygonSmoothing.chart Q
      (arithmeticZeroThirdLastSmoothing hπ data H 0 hj u hu m b)
  | .terminal => PolygonSmoothing.chart Q
      (arithmeticZeroThirdTerminalSmoothing hπ data H 0 hj u hu m)
  | .infinity => B .infinity

local notation "A" => arithmeticZeroThirdAtlasObject hπ data H m hj u hu

/-- All third factors are installed together from the same second atlas. -/
def arithmeticZeroThirdAtlasCorrection (i : ArithmeticChartLabel 1) : B i ≅ A i :=
  match i with
  | .initial b => arithmeticZeroThirdInitialIso hπ data H m 0 hj u hu b
  | .retained ⟨0, _⟩ b => arithmeticZeroThirdLastIso hπ data H m 0 hj u hu b
  | .retained ⟨k + 1, hk⟩ _ => False.elim (by omega)
  | .terminal => arithmeticZeroThirdTerminalIso hπ data H m 0 hj u hu
  | .infinity => Iso.refl _

attribute [local irreducible] arithmeticZeroThirdAtlasCorrection
local notation "E" => arithmeticZeroThirdAtlasCorrection hπ data H m hj u hu

/-- The full third chart inclusion in the unchanged global target. -/
def arithmeticZeroThirdAtlasChart (i : ArithmeticChartLabel 1) :
    A i ⟶ simultaneousTwistedArithmeticStage hπ data H m 0 hj u hu :=
  (E i).inv ≫ κ i

instance arithmeticZeroThirdAtlasChart_isOpenImmersion (i : ArithmeticChartLabel 1) :
    IsOpenImmersion (arithmeticZeroThirdAtlasChart hπ data H m hj u hu i) := by
  unfold arithmeticZeroThirdAtlasChart
  infer_instance

/-- The comparison from each original chart includes all accumulated complete correction rounds. -/
def arithmeticZeroThirdAtlasIso (i : ArithmeticChartLabel 1) :
    arithmeticLabeledAtlasObject hπ data H m 1 hj i ≅ A i := I i ≪≫ E i

local notation "ι" => arithmeticZeroThirdAtlasChart hπ data H m hj u hu

/-- The installed correction recovers the exact second inclusion at every label. -/
@[reassoc] theorem arithmeticZeroThirdAtlasCorrection_chart (i : ArithmeticChartLabel 1) :
    (E i).hom ≫ ι i = κ i := by
  rw [arithmeticZeroThirdAtlasChart, Iso.hom_inv_id_assoc]

/-- The original global inclusion is recovered by the composed full chart comparison. -/
@[reassoc] theorem arithmeticZeroThirdAtlasIso_chart (i : ArithmeticChartLabel 1) :
    arithmeticLabeledAtlasMap hπ data H m 1 hj i ≫
        (simultaneousTwistedArithmeticIso hπ data H m 0 hj u hu).hom =
      (arithmeticZeroThirdAtlasIso hπ data H m hj u hu i).hom ≫ ι i := by
  rw [arithmeticZeroThirdAtlasIso, Iso.trans_hom, Category.assoc,
    arithmeticZeroThirdAtlasCorrection_chart]
  exact arithmeticZeroSecondAtlasIso_chart hπ data H m hj u hu i

attribute [local irreducible] arithmeticZeroThirdAtlasChart

/-- The simultaneous third factors transport the entire original cover. -/
def arithmeticZeroThirdOpenCover :
    (simultaneousTwistedArithmeticStage hπ data H m 0 hj u hu).OpenCover :=
  (arithmeticZeroSecondOpenCover hπ data H m hj u hu).copy
    (ArithmeticChartLabel 1) A ι (Equiv.refl _) (fun i ↦ (E i).symm)
      (fun _ ↦ by rw [arithmeticZeroThirdAtlasChart]; rfl)

/-- Every point of the full global target remains covered by a third chart. -/
theorem arithmeticZeroThirdAtlas_cover
    (z : simultaneousTwistedArithmeticStage hπ data H m 0 hj u hu) :
    ∃ i x, ι i x = z := (arithmeticZeroThirdOpenCover hπ data H m hj u hu).exists_eq z

end FLT.Mazur.WeierstrassDividedDepth
