/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroFiniteGeometry
public import FLT.Mazur.WeierstrassDividedZeroFifthAtlas

/-!
# Install the complete finite depth-zero correction atlas

The original initial open and the unique last node receive the two full finite
factors. The same common terminal receives both closing corrections on its full fifth smoothing.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFifthAtlasChart arithmeticZeroFiniteInitialIso arithmeticZeroFiniteLastIso
  arithmeticZeroFiniteTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (k m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "B" => arithmeticZeroFifthAtlasObject hπ data H m hj u hu
local notation "κ" => arithmeticZeroFifthAtlasChart hπ data H m hj u hu
local notation "I" => arithmeticZeroFifthAtlasIso hπ data H m hj u hu

/-- The finite objects at each actual depth-zero label, including the original infinity. -/
def arithmeticZeroFiniteAtlasObject : ArithmeticChartLabel 1 → Scheme
  | .initial b => arithmeticZeroFiniteInitialObject hπ data H k m 0 hj u hu b
  | .retained _ b => PolygonSmoothing.chart Q
      ((arithmeticZeroFiniteState hπ data H 0 hj u hu k).last m b)
  | .terminal => PolygonSmoothing.chart Q
      ((arithmeticZeroFiniteState hπ data H 0 hj u hu k).terminal m)
  | .infinity => B .infinity

local notation "A" => arithmeticZeroFiniteAtlasObject hπ data H k m hj u hu

/-- All finite factors are installed together from the same fifth atlas. -/
def arithmeticZeroFiniteAtlasCorrection (i : ArithmeticChartLabel 1) : B i ≅ A i :=
  match i with
  | .initial b => arithmeticZeroFiniteInitialIso hπ data H k m 0 hj u hu b
  | .retained ⟨0, _⟩ b => arithmeticZeroFiniteLastIso hπ data H k m 0 hj u hu b
  | .retained ⟨k + 1, hk⟩ _ => False.elim (by omega)
  | .terminal => arithmeticZeroFiniteTerminalIso hπ data H k m 0 hj u hu
  | .infinity => Iso.refl _

attribute [local irreducible] arithmeticZeroFiniteAtlasCorrection
local notation "E" => arithmeticZeroFiniteAtlasCorrection hπ data H k m hj u hu

/-- The full finite chart inclusion in the unchanged global target. -/
def arithmeticZeroFiniteAtlasChart (i : ArithmeticChartLabel 1) :
    A i ⟶ simultaneousTwistedArithmeticStage hπ data H m 0 hj u hu :=
  (E i).inv ≫ κ i

instance arithmeticZeroFiniteAtlasChart_isOpenImmersion (i : ArithmeticChartLabel 1) :
    IsOpenImmersion (arithmeticZeroFiniteAtlasChart hπ data H k m hj u hu i) := by
  unfold arithmeticZeroFiniteAtlasChart
  infer_instance

/-- The comparison from each original chart includes all accumulated complete correction rounds. -/
def arithmeticZeroFiniteAtlasIso (i : ArithmeticChartLabel 1) :
    arithmeticLabeledAtlasObject hπ data H m 1 hj i ≅ A i := I i ≪≫ E i

local notation "ι" => arithmeticZeroFiniteAtlasChart hπ data H k m hj u hu

/-- The installed correction recovers the exact fifth inclusion at every label. -/
@[reassoc] theorem arithmeticZeroFiniteAtlasCorrection_chart (i : ArithmeticChartLabel 1) :
    (E i).hom ≫ ι i = κ i := by
  rw [arithmeticZeroFiniteAtlasChart, Iso.hom_inv_id_assoc]

/-- The original global inclusion is recovered by the composed full chart comparison. -/
@[reassoc] theorem arithmeticZeroFiniteAtlasIso_chart (i : ArithmeticChartLabel 1) :
    arithmeticLabeledAtlasMap hπ data H m 1 hj i ≫
        (simultaneousTwistedArithmeticIso hπ data H m 0 hj u hu).hom =
      (arithmeticZeroFiniteAtlasIso hπ data H k m hj u hu i).hom ≫ ι i := by
  rw [arithmeticZeroFiniteAtlasIso, Iso.trans_hom, Category.assoc,
    arithmeticZeroFiniteAtlasCorrection_chart]
  exact arithmeticZeroFifthAtlasIso_chart hπ data H m hj u hu i

attribute [local irreducible] arithmeticZeroFiniteAtlasChart

/-- The simultaneous finite factors transport the entire original cover. -/
def arithmeticZeroFiniteOpenCover :
    (simultaneousTwistedArithmeticStage hπ data H m 0 hj u hu).OpenCover :=
  (arithmeticZeroFifthOpenCover hπ data H m hj u hu).copy
    (ArithmeticChartLabel 1) A ι (Equiv.refl _) (fun i ↦ (E i).symm)
      (fun _ ↦ by rw [arithmeticZeroFiniteAtlasChart]; rfl)

/-- Every point of the full global target remains covered by a finite chart. -/
theorem arithmeticZeroFiniteAtlas_cover
    (z : simultaneousTwistedArithmeticStage hπ data H m 0 hj u hu) :
    ∃ i x, ι i x = z := (arithmeticZeroFiniteOpenCover hπ data H k m hj u hu).exists_eq z

end FLT.Mazur.WeierstrassDividedDepth
