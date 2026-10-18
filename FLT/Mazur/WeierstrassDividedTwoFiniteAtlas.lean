/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTwoFiniteGeometry
public import FLT.Mazur.WeierstrassDividedFifthShallowAtlas

/-!
# Install the complete finite depth-two correction atlas

The original initial open and all three retained nodes receive their full finite
factors. The same common terminal receives both closing corrections on its full fifth smoothing.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFifthShallowAtlasChart arithmeticTwoFiniteInitialIso arithmeticTwoFiniteRetainedIso
  arithmeticTwoFiniteTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (k m : ℕ) (hj : 3 ≤ n)
  (u : Rˣ) (hu : (data ⟨3, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "B" => arithmeticFifthShallowAtlasObject hπ data H m hj u hu
local notation "κ" => arithmeticFifthShallowAtlasChart hπ data H m hj u hu
local notation "I" => arithmeticFifthShallowAtlasIso hπ data H m hj u hu

/-- The finite objects at each actual depth-two label, including the original infinity. -/
def arithmeticTwoFiniteAtlasObject : ArithmeticChartLabel 3 → Scheme
  | .initial b => arithmeticTwoFiniteInitialObject hπ data H k m hj u hu b
  | .retained i b => PolygonSmoothing.chart Q
      ((arithmeticTwoFiniteState hπ data H hj u hu k).retained m i b)
  | .terminal => PolygonSmoothing.chart Q
      ((arithmeticTwoFiniteState hπ data H hj u hu k).terminal m)
  | .infinity => B .infinity

local notation "A" => arithmeticTwoFiniteAtlasObject hπ data H k m hj u hu

/-- All finite factors are installed together from the same fifth atlas. -/
def arithmeticTwoFiniteAtlasCorrection (i : ArithmeticChartLabel 3) : B i ≅ A i :=
  match i with
  | .initial b => arithmeticTwoFiniteInitialIso hπ data H k m hj u hu b
  | .retained ⟨0, _⟩ b => arithmeticTwoFiniteRetainedIso hπ data H k m hj u hu 0 b
  | .retained ⟨1, _⟩ b => arithmeticTwoFiniteRetainedIso hπ data H k m hj u hu 1 b
  | .retained ⟨2, _⟩ b => (twistedRetainedOrientation data H m b).symm ≪≫
      arithmeticTwoFiniteRetainedIso hπ data H k m hj u hu 2 b
  | .retained ⟨a + 3, ha⟩ _ => False.elim (by omega)
  | .terminal => arithmeticTwoFiniteTerminalIso hπ data H k m hj u hu
  | .infinity => Iso.refl _

attribute [local irreducible] arithmeticTwoFiniteAtlasCorrection
local notation "E" => arithmeticTwoFiniteAtlasCorrection hπ data H k m hj u hu

/-- The full finite chart inclusion in the unchanged global target. -/
def arithmeticTwoFiniteAtlasChart (i : ArithmeticChartLabel 3) :
    A i ⟶ simultaneousTwistedArithmeticStage hπ data H m 2 hj u hu :=
  (E i).inv ≫ κ i

instance arithmeticTwoFiniteAtlasChart_isOpenImmersion (i : ArithmeticChartLabel 3) :
    IsOpenImmersion (arithmeticTwoFiniteAtlasChart hπ data H k m hj u hu i) := by
  unfold arithmeticTwoFiniteAtlasChart
  infer_instance

/-- The comparison from each original chart includes all accumulated complete correction rounds. -/
def arithmeticTwoFiniteAtlasIso (i : ArithmeticChartLabel 3) :
    arithmeticLabeledAtlasObject hπ data H m 3 hj i ≅ A i := I i ≪≫ E i

local notation "ι" => arithmeticTwoFiniteAtlasChart hπ data H k m hj u hu

/-- The installed correction recovers the exact fifth inclusion at every label. -/
@[reassoc] theorem arithmeticTwoFiniteAtlasCorrection_chart (i : ArithmeticChartLabel 3) :
    (E i).hom ≫ ι i = κ i := by
  rw [arithmeticTwoFiniteAtlasChart, Iso.hom_inv_id_assoc]

/-- The original global inclusion is recovered by the composed full chart comparison. -/
@[reassoc] theorem arithmeticTwoFiniteAtlasIso_chart (i : ArithmeticChartLabel 3) :
    arithmeticLabeledAtlasMap hπ data H m 3 hj i ≫
        (simultaneousTwistedArithmeticIso hπ data H m 2 hj u hu).hom =
      (arithmeticTwoFiniteAtlasIso hπ data H k m hj u hu i).hom ≫ ι i := by
  rw [arithmeticTwoFiniteAtlasIso, Iso.trans_hom, Category.assoc,
    arithmeticTwoFiniteAtlasCorrection_chart]
  exact arithmeticFifthShallowAtlasIso_chart hπ data H m hj u hu i

attribute [local irreducible] arithmeticTwoFiniteAtlasChart

/-- The simultaneous finite factors transport the entire original cover. -/
def arithmeticTwoFiniteOpenCover :
    (simultaneousTwistedArithmeticStage hπ data H m 2 hj u hu).OpenCover :=
  (arithmeticFifthShallowOpenCover hπ data H m hj u hu).copy
    (ArithmeticChartLabel 3) A ι (Equiv.refl _) (fun i ↦ (E i).symm)
      (fun _ ↦ by rw [arithmeticTwoFiniteAtlasChart]; rfl)

/-- Every point of the full global target remains covered by a finite chart. -/
theorem arithmeticTwoFiniteAtlas_cover
    (z : simultaneousTwistedArithmeticStage hπ data H m 2 hj u hu) :
    ∃ i x, ι i x = z := (arithmeticTwoFiniteOpenCover hπ data H k m hj u hu).exists_eq z

end FLT.Mazur.WeierstrassDividedDepth
