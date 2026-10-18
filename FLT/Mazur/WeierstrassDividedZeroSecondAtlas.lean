/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroSecondGeometry
public import FLT.Mazur.WeierstrassDividedZeroFirstAtlas

/-!
# Install the complete second depth-zero correction atlas

The original initial open and the unique last node receive the two full second
factors. The same common terminal receives both closing corrections on its full first smoothing.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFirstAtlasChart arithmeticZeroSecondInitialIso arithmeticZeroSecondLastIso
  arithmeticZeroSecondTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "B" => arithmeticZeroFirstAtlasObject hπ data H m hj u hu
local notation "κ" => arithmeticZeroFirstAtlasChart hπ data H m hj u hu
local notation "I" => arithmeticZeroFirstAtlasIso hπ data H m hj u hu

/-- The second objects at each actual depth-zero label, including the original infinity. -/
def arithmeticZeroSecondAtlasObject : ArithmeticChartLabel 1 → Scheme
  | .initial b => arithmeticZeroSecondInitialObject hπ data H m 0 hj u hu b
  | .retained _ b => PolygonSmoothing.chart Q
      (arithmeticZeroSecondLastSmoothing hπ data H 0 hj u hu m b)
  | .terminal => PolygonSmoothing.chart Q
      (arithmeticZeroSecondTerminalSmoothing hπ data H 0 hj u hu m)
  | .infinity => B .infinity

local notation "A" => arithmeticZeroSecondAtlasObject hπ data H m hj u hu

/-- All second factors are installed together from the same first atlas. -/
def arithmeticZeroSecondAtlasCorrection (i : ArithmeticChartLabel 1) : B i ≅ A i :=
  match i with
  | .initial b => arithmeticZeroSecondInitialIso hπ data H m 0 hj u hu b
  | .retained ⟨0, _⟩ b => arithmeticZeroSecondLastIso hπ data H m 0 hj u hu b
  | .retained ⟨k + 1, hk⟩ _ => False.elim (by omega)
  | .terminal => arithmeticZeroSecondTerminalIso hπ data H m 0 hj u hu
  | .infinity => Iso.refl _

attribute [local irreducible] arithmeticZeroSecondAtlasCorrection
local notation "E" => arithmeticZeroSecondAtlasCorrection hπ data H m hj u hu

/-- The full second chart inclusion in the unchanged global target. -/
def arithmeticZeroSecondAtlasChart (i : ArithmeticChartLabel 1) :
    A i ⟶ simultaneousTwistedArithmeticStage hπ data H m 0 hj u hu :=
  (E i).inv ≫ κ i

instance arithmeticZeroSecondAtlasChart_isOpenImmersion (i : ArithmeticChartLabel 1) :
    IsOpenImmersion (arithmeticZeroSecondAtlasChart hπ data H m hj u hu i) := by
  unfold arithmeticZeroSecondAtlasChart
  infer_instance

/-- The comparison from each original chart includes all accumulated complete correction rounds. -/
def arithmeticZeroSecondAtlasIso (i : ArithmeticChartLabel 1) :
    arithmeticLabeledAtlasObject hπ data H m 1 hj i ≅ A i := I i ≪≫ E i

local notation "ι" => arithmeticZeroSecondAtlasChart hπ data H m hj u hu

/-- The installed correction recovers the exact first inclusion at every label. -/
@[reassoc] theorem arithmeticZeroSecondAtlasCorrection_chart (i : ArithmeticChartLabel 1) :
    (E i).hom ≫ ι i = κ i := by
  rw [arithmeticZeroSecondAtlasChart, Iso.hom_inv_id_assoc]

/-- The original global inclusion is recovered by the composed full chart comparison. -/
@[reassoc] theorem arithmeticZeroSecondAtlasIso_chart (i : ArithmeticChartLabel 1) :
    arithmeticLabeledAtlasMap hπ data H m 1 hj i ≫
        (simultaneousTwistedArithmeticIso hπ data H m 0 hj u hu).hom =
      (arithmeticZeroSecondAtlasIso hπ data H m hj u hu i).hom ≫ ι i := by
  rw [arithmeticZeroSecondAtlasIso, Iso.trans_hom, Category.assoc,
    arithmeticZeroSecondAtlasCorrection_chart]
  exact arithmeticZeroFirstAtlasIso_chart hπ data H m hj u hu i

attribute [local irreducible] arithmeticZeroSecondAtlasChart

/-- The simultaneous second factors transport the entire original cover. -/
def arithmeticZeroSecondOpenCover :
    (simultaneousTwistedArithmeticStage hπ data H m 0 hj u hu).OpenCover :=
  (arithmeticZeroFirstOpenCover hπ data H m hj u hu).copy
    (ArithmeticChartLabel 1) A ι (Equiv.refl _) (fun i ↦ (E i).symm)
      (fun _ ↦ by rw [arithmeticZeroSecondAtlasChart]; rfl)

/-- Every point of the full global target remains covered by a second chart. -/
theorem arithmeticZeroSecondAtlas_cover
    (z : simultaneousTwistedArithmeticStage hπ data H m 0 hj u hu) :
    ∃ i x, ι i x = z := (arithmeticZeroSecondOpenCover hπ data H m hj u hu).exists_eq z

end FLT.Mazur.WeierstrassDividedDepth
