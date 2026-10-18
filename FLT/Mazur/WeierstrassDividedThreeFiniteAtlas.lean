/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThreeFiniteGeometry
public import FLT.Mazur.WeierstrassDividedThreeSeedAtlas

/-!
# Install the complete finite depth-three correction atlas

The original initial open and all four retained nodes receive their full finite
factors. The same common terminal receives both closing corrections on its full fifth smoothing.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticThreeSeedAtlasChart arithmeticThreeFiniteInitialIso arithmeticThreeFiniteRetainedIso
  arithmeticThreeFiniteTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (k m : ℕ) (hj : 4 ≤ n)
  (u : Rˣ) (hu : (data ⟨4, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "B" => arithmeticThreeSeedAtlasObject hπ data H m hj u hu
local notation "κ" => arithmeticThreeSeedAtlasChart hπ data H m hj u hu
local notation "I" => arithmeticThreeSeedAtlasIso hπ data H m hj u hu

/-- The finite objects at each actual depth-three label, including the original infinity. -/
def arithmeticThreeFiniteAtlasObject : ArithmeticChartLabel 4 → Scheme
  | .initial b => arithmeticThreeFiniteInitialObject hπ data H k m hj u hu b
  | .retained i b => PolygonSmoothing.chart Q
      ((arithmeticThreeFiniteState hπ data H hj u hu k).retained m i b)
  | .terminal => PolygonSmoothing.chart Q
      ((arithmeticThreeFiniteState hπ data H hj u hu k).terminal m)
  | .infinity => B .infinity

local notation "A" => arithmeticThreeFiniteAtlasObject hπ data H k m hj u hu

/-- All finite factors are installed together from the same fifth atlas. -/
def arithmeticThreeFiniteAtlasCorrection (i : ArithmeticChartLabel 4) : B i ≅ A i :=
  match i with
  | .initial b => arithmeticThreeFiniteInitialIso hπ data H k m hj u hu b
  | .retained i b => arithmeticThreeFiniteRetainedIso hπ data H k m hj u hu i b
  | .terminal => arithmeticThreeFiniteTerminalIso hπ data H k m hj u hu
  | .infinity => Iso.refl _

attribute [local irreducible] arithmeticThreeFiniteAtlasCorrection
local notation "E" => arithmeticThreeFiniteAtlasCorrection hπ data H k m hj u hu

/-- The full finite chart inclusion in the unchanged global target. -/
def arithmeticThreeFiniteAtlasChart (i : ArithmeticChartLabel 4) :
    A i ⟶ simultaneousTwistedArithmeticStage hπ data H m 3 hj u hu :=
  (E i).inv ≫ κ i

instance arithmeticThreeFiniteAtlasChart_isOpenImmersion (i : ArithmeticChartLabel 4) :
    IsOpenImmersion (arithmeticThreeFiniteAtlasChart hπ data H k m hj u hu i) := by
  unfold arithmeticThreeFiniteAtlasChart
  infer_instance

/-- The comparison from each original chart includes all accumulated complete correction rounds. -/
def arithmeticThreeFiniteAtlasIso (i : ArithmeticChartLabel 4) :
    arithmeticLabeledAtlasObject hπ data H m 4 hj i ≅ A i := I i ≪≫ E i

local notation "ι" => arithmeticThreeFiniteAtlasChart hπ data H k m hj u hu

/-- The installed correction recovers the exact fifth inclusion at every label. -/
@[reassoc] theorem arithmeticThreeFiniteAtlasCorrection_chart (i : ArithmeticChartLabel 4) :
    (E i).hom ≫ ι i = κ i := by
  rw [arithmeticThreeFiniteAtlasChart, Iso.hom_inv_id_assoc]

/-- The original global inclusion is recovered by the composed full chart comparison. -/
@[reassoc] theorem arithmeticThreeFiniteAtlasIso_chart (i : ArithmeticChartLabel 4) :
    arithmeticLabeledAtlasMap hπ data H m 4 hj i ≫
        (simultaneousTwistedArithmeticIso hπ data H m 3 hj u hu).hom =
      (arithmeticThreeFiniteAtlasIso hπ data H k m hj u hu i).hom ≫ ι i := by
  rw [arithmeticThreeFiniteAtlasIso, Iso.trans_hom, Category.assoc,
    arithmeticThreeFiniteAtlasCorrection_chart]
  exact arithmeticThreeSeedAtlasIso_chart hπ data H m hj u hu i

attribute [local irreducible] arithmeticThreeFiniteAtlasChart

/-- The simultaneous finite factors transport the entire original cover. -/
def arithmeticThreeFiniteOpenCover :
    (simultaneousTwistedArithmeticStage hπ data H m 3 hj u hu).OpenCover :=
  (arithmeticThreeSeedOpenCover hπ data H m hj u hu).copy
    (ArithmeticChartLabel 4) A ι (Equiv.refl _) (fun i ↦ (E i).symm)
      (fun _ ↦ by rw [arithmeticThreeFiniteAtlasChart]; rfl)

/-- Every point of the full global target remains covered by a finite chart. -/
theorem arithmeticThreeFiniteAtlas_cover
    (z : simultaneousTwistedArithmeticStage hπ data H m 3 hj u hu) :
    ∃ i x, ι i x = z := (arithmeticThreeFiniteOpenCover hπ data H k m hj u hu).exists_eq z

end FLT.Mazur.WeierstrassDividedDepth
