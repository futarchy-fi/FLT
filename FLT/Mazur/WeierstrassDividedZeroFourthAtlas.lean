/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroFourthGeometry
public import FLT.Mazur.WeierstrassDividedZeroThirdAtlas

/-!
# Install the complete fourth depth-zero correction atlas

The original initial open and the unique last node receive the two full fourth
factors. The same common terminal receives both closing corrections on its full third smoothing.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroThirdAtlasChart arithmeticZeroFourthInitialIso arithmeticZeroFourthLastIso
  arithmeticZeroFourthTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "B" => arithmeticZeroThirdAtlasObject hπ data H m hj u hu
local notation "κ" => arithmeticZeroThirdAtlasChart hπ data H m hj u hu
local notation "I" => arithmeticZeroThirdAtlasIso hπ data H m hj u hu

/-- The fourth objects at each actual depth-zero label, including the original infinity. -/
def arithmeticZeroFourthAtlasObject : ArithmeticChartLabel 1 → Scheme
  | .initial b => arithmeticZeroFourthInitialObject hπ data H m 0 hj u hu b
  | .retained _ b => PolygonSmoothing.chart Q
      (arithmeticZeroFourthLastSmoothing hπ data H 0 hj u hu m b)
  | .terminal => PolygonSmoothing.chart Q
      (arithmeticZeroFourthTerminalSmoothing hπ data H 0 hj u hu m)
  | .infinity => B .infinity

local notation "A" => arithmeticZeroFourthAtlasObject hπ data H m hj u hu

/-- All fourth factors are installed together from the same third atlas. -/
def arithmeticZeroFourthAtlasCorrection (i : ArithmeticChartLabel 1) : B i ≅ A i :=
  match i with
  | .initial b => arithmeticZeroFourthInitialIso hπ data H m 0 hj u hu b
  | .retained ⟨0, _⟩ b => arithmeticZeroFourthLastIso hπ data H m 0 hj u hu b
  | .retained ⟨k + 1, hk⟩ _ => False.elim (by omega)
  | .terminal => arithmeticZeroFourthTerminalIso hπ data H m 0 hj u hu
  | .infinity => Iso.refl _

attribute [local irreducible] arithmeticZeroFourthAtlasCorrection
local notation "E" => arithmeticZeroFourthAtlasCorrection hπ data H m hj u hu

/-- The full fourth chart inclusion in the unchanged global target. -/
def arithmeticZeroFourthAtlasChart (i : ArithmeticChartLabel 1) :
    A i ⟶ simultaneousTwistedArithmeticStage hπ data H m 0 hj u hu :=
  (E i).inv ≫ κ i

instance arithmeticZeroFourthAtlasChart_isOpenImmersion (i : ArithmeticChartLabel 1) :
    IsOpenImmersion (arithmeticZeroFourthAtlasChart hπ data H m hj u hu i) := by
  unfold arithmeticZeroFourthAtlasChart
  infer_instance

/-- The comparison from each original chart includes all accumulated complete correction rounds. -/
def arithmeticZeroFourthAtlasIso (i : ArithmeticChartLabel 1) :
    arithmeticLabeledAtlasObject hπ data H m 1 hj i ≅ A i := I i ≪≫ E i

local notation "ι" => arithmeticZeroFourthAtlasChart hπ data H m hj u hu

/-- The installed correction recovers the exact third inclusion at every label. -/
@[reassoc] theorem arithmeticZeroFourthAtlasCorrection_chart (i : ArithmeticChartLabel 1) :
    (E i).hom ≫ ι i = κ i := by
  rw [arithmeticZeroFourthAtlasChart, Iso.hom_inv_id_assoc]

/-- The original global inclusion is recovered by the composed full chart comparison. -/
@[reassoc] theorem arithmeticZeroFourthAtlasIso_chart (i : ArithmeticChartLabel 1) :
    arithmeticLabeledAtlasMap hπ data H m 1 hj i ≫
        (simultaneousTwistedArithmeticIso hπ data H m 0 hj u hu).hom =
      (arithmeticZeroFourthAtlasIso hπ data H m hj u hu i).hom ≫ ι i := by
  rw [arithmeticZeroFourthAtlasIso, Iso.trans_hom, Category.assoc,
    arithmeticZeroFourthAtlasCorrection_chart]
  exact arithmeticZeroThirdAtlasIso_chart hπ data H m hj u hu i

attribute [local irreducible] arithmeticZeroFourthAtlasChart

/-- The simultaneous fourth factors transport the entire original cover. -/
def arithmeticZeroFourthOpenCover :
    (simultaneousTwistedArithmeticStage hπ data H m 0 hj u hu).OpenCover :=
  (arithmeticZeroThirdOpenCover hπ data H m hj u hu).copy
    (ArithmeticChartLabel 1) A ι (Equiv.refl _) (fun i ↦ (E i).symm)
      (fun _ ↦ by rw [arithmeticZeroFourthAtlasChart]; rfl)

/-- Every point of the full global target remains covered by a fourth chart. -/
theorem arithmeticZeroFourthAtlas_cover
    (z : simultaneousTwistedArithmeticStage hπ data H m 0 hj u hu) :
    ∃ i x, ι i x = z := (arithmeticZeroFourthOpenCover hπ data H m hj u hu).exists_eq z

end FLT.Mazur.WeierstrassDividedDepth
