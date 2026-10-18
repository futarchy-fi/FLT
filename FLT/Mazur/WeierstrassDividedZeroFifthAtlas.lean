/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroFifthGeometry
public import FLT.Mazur.WeierstrassDividedZeroFourthAtlas

/-!
# Install the complete fifth depth-zero correction atlas

The original initial open and the unique last node receive the two full fifth
factors. The same common terminal receives both closing corrections on its full fourth smoothing.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFourthAtlasChart arithmeticZeroFifthInitialIso arithmeticZeroFifthLastIso
  arithmeticZeroFifthTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "B" => arithmeticZeroFourthAtlasObject hπ data H m hj u hu
local notation "κ" => arithmeticZeroFourthAtlasChart hπ data H m hj u hu
local notation "I" => arithmeticZeroFourthAtlasIso hπ data H m hj u hu

/-- The fifth objects at each actual depth-zero label, including the original infinity. -/
def arithmeticZeroFifthAtlasObject : ArithmeticChartLabel 1 → Scheme
  | .initial b => arithmeticZeroFifthInitialObject hπ data H m 0 hj u hu b
  | .retained _ b => PolygonSmoothing.chart Q
      (arithmeticZeroFifthLastSmoothing hπ data H 0 hj u hu m b)
  | .terminal => PolygonSmoothing.chart Q
      (arithmeticZeroFifthTerminalSmoothing hπ data H 0 hj u hu m)
  | .infinity => B .infinity

local notation "A" => arithmeticZeroFifthAtlasObject hπ data H m hj u hu

/-- All fifth factors are installed together from the same fourth atlas. -/
def arithmeticZeroFifthAtlasCorrection (i : ArithmeticChartLabel 1) : B i ≅ A i :=
  match i with
  | .initial b => arithmeticZeroFifthInitialIso hπ data H m 0 hj u hu b
  | .retained ⟨0, _⟩ b => arithmeticZeroFifthLastIso hπ data H m 0 hj u hu b
  | .retained ⟨k + 1, hk⟩ _ => False.elim (by omega)
  | .terminal => arithmeticZeroFifthTerminalIso hπ data H m 0 hj u hu
  | .infinity => Iso.refl _

attribute [local irreducible] arithmeticZeroFifthAtlasCorrection
local notation "E" => arithmeticZeroFifthAtlasCorrection hπ data H m hj u hu

/-- The full fifth chart inclusion in the unchanged global target. -/
def arithmeticZeroFifthAtlasChart (i : ArithmeticChartLabel 1) :
    A i ⟶ simultaneousTwistedArithmeticStage hπ data H m 0 hj u hu :=
  (E i).inv ≫ κ i

instance arithmeticZeroFifthAtlasChart_isOpenImmersion (i : ArithmeticChartLabel 1) :
    IsOpenImmersion (arithmeticZeroFifthAtlasChart hπ data H m hj u hu i) := by
  unfold arithmeticZeroFifthAtlasChart
  infer_instance

/-- The comparison from each original chart includes all accumulated complete correction rounds. -/
def arithmeticZeroFifthAtlasIso (i : ArithmeticChartLabel 1) :
    arithmeticLabeledAtlasObject hπ data H m 1 hj i ≅ A i := I i ≪≫ E i

local notation "ι" => arithmeticZeroFifthAtlasChart hπ data H m hj u hu

/-- The installed correction recovers the exact fourth inclusion at every label. -/
@[reassoc] theorem arithmeticZeroFifthAtlasCorrection_chart (i : ArithmeticChartLabel 1) :
    (E i).hom ≫ ι i = κ i := by
  rw [arithmeticZeroFifthAtlasChart, Iso.hom_inv_id_assoc]

/-- The original global inclusion is recovered by the composed full chart comparison. -/
@[reassoc] theorem arithmeticZeroFifthAtlasIso_chart (i : ArithmeticChartLabel 1) :
    arithmeticLabeledAtlasMap hπ data H m 1 hj i ≫
        (simultaneousTwistedArithmeticIso hπ data H m 0 hj u hu).hom =
      (arithmeticZeroFifthAtlasIso hπ data H m hj u hu i).hom ≫ ι i := by
  rw [arithmeticZeroFifthAtlasIso, Iso.trans_hom, Category.assoc,
    arithmeticZeroFifthAtlasCorrection_chart]
  exact arithmeticZeroFourthAtlasIso_chart hπ data H m hj u hu i

attribute [local irreducible] arithmeticZeroFifthAtlasChart

/-- The simultaneous fifth factors transport the entire original cover. -/
def arithmeticZeroFifthOpenCover :
    (simultaneousTwistedArithmeticStage hπ data H m 0 hj u hu).OpenCover :=
  (arithmeticZeroFourthOpenCover hπ data H m hj u hu).copy
    (ArithmeticChartLabel 1) A ι (Equiv.refl _) (fun i ↦ (E i).symm)
      (fun _ ↦ by rw [arithmeticZeroFifthAtlasChart]; rfl)

/-- Every point of the full global target remains covered by a fifth chart. -/
theorem arithmeticZeroFifthAtlas_cover
    (z : simultaneousTwistedArithmeticStage hπ data H m 0 hj u hu) :
    ∃ i x, ι i x = z := (arithmeticZeroFifthOpenCover hπ data H m hj u hu).exists_eq z

end FLT.Mazur.WeierstrassDividedDepth
