/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOneFiniteGeometry
public import FLT.Mazur.WeierstrassDividedFifthInitialAtlas

/-!
# Install the complete finite depth-one correction atlas

The original initial open and both retained nodes receive their full finite
factors. The same common terminal receives both closing corrections on its full fifth smoothing.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFifthInitialAtlasChart arithmeticOneFiniteInitialIso arithmeticOneFiniteRetainedIso
  arithmeticOneFiniteTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (k m : ℕ) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "B" => arithmeticFifthInitialAtlasObject hπ data H m hj u hu
local notation "κ" => arithmeticFifthInitialAtlasChart hπ data H m hj u hu
local notation "I" => arithmeticFifthInitialAtlasIso hπ data H m hj u hu

/-- The finite objects at each actual depth-one label, including the original infinity. -/
def arithmeticOneFiniteAtlasObject : ArithmeticChartLabel 2 → Scheme
  | .initial b => arithmeticOneFiniteInitialObject hπ data H k m hj u hu b
  | .retained i b => PolygonSmoothing.chart Q
      ((arithmeticOneFiniteState hπ data H hj u hu k).retained m i b)
  | .terminal => PolygonSmoothing.chart Q
      ((arithmeticOneFiniteState hπ data H hj u hu k).terminal m)
  | .infinity => B .infinity

local notation "A" => arithmeticOneFiniteAtlasObject hπ data H k m hj u hu

/-- All finite factors are installed together from the same fifth atlas. -/
def arithmeticOneFiniteAtlasCorrection (i : ArithmeticChartLabel 2) : B i ≅ A i :=
  match i with
  | .initial b => arithmeticOneFiniteInitialIso hπ data H k m hj u hu b
  | .retained ⟨0, _⟩ b => arithmeticOneFiniteRetainedIso hπ data H k m hj u hu 0 b
  | .retained ⟨1, _⟩ b => (twistedRetainedOrientation data H m b).symm ≪≫
      arithmeticOneFiniteRetainedIso hπ data H k m hj u hu 1 b
  | .retained ⟨a + 2, ha⟩ _ => False.elim (by omega)
  | .terminal => arithmeticOneFiniteTerminalIso hπ data H k m hj u hu
  | .infinity => Iso.refl _

attribute [local irreducible] arithmeticOneFiniteAtlasCorrection
local notation "E" => arithmeticOneFiniteAtlasCorrection hπ data H k m hj u hu

/-- The full finite chart inclusion in the unchanged global target. -/
def arithmeticOneFiniteAtlasChart (i : ArithmeticChartLabel 2) :
    A i ⟶ simultaneousTwistedArithmeticStage hπ data H m 1 hj u hu :=
  (E i).inv ≫ κ i

instance arithmeticOneFiniteAtlasChart_isOpenImmersion (i : ArithmeticChartLabel 2) :
    IsOpenImmersion (arithmeticOneFiniteAtlasChart hπ data H k m hj u hu i) := by
  unfold arithmeticOneFiniteAtlasChart
  infer_instance

/-- The comparison from each original chart includes all accumulated complete correction rounds. -/
def arithmeticOneFiniteAtlasIso (i : ArithmeticChartLabel 2) :
    arithmeticLabeledAtlasObject hπ data H m 2 hj i ≅ A i := I i ≪≫ E i

local notation "ι" => arithmeticOneFiniteAtlasChart hπ data H k m hj u hu

/-- The installed correction recovers the exact fifth inclusion at every label. -/
@[reassoc] theorem arithmeticOneFiniteAtlasCorrection_chart (i : ArithmeticChartLabel 2) :
    (E i).hom ≫ ι i = κ i := by
  rw [arithmeticOneFiniteAtlasChart, Iso.hom_inv_id_assoc]

/-- The original global inclusion is recovered by the composed full chart comparison. -/
@[reassoc] theorem arithmeticOneFiniteAtlasIso_chart (i : ArithmeticChartLabel 2) :
    arithmeticLabeledAtlasMap hπ data H m 2 hj i ≫
        (simultaneousTwistedArithmeticIso hπ data H m 1 hj u hu).hom =
      (arithmeticOneFiniteAtlasIso hπ data H k m hj u hu i).hom ≫ ι i := by
  rw [arithmeticOneFiniteAtlasIso, Iso.trans_hom, Category.assoc,
    arithmeticOneFiniteAtlasCorrection_chart]
  exact arithmeticFifthInitialAtlasIso_chart hπ data H m hj u hu i

attribute [local irreducible] arithmeticOneFiniteAtlasChart

/-- The simultaneous finite factors transport the entire original cover. -/
def arithmeticOneFiniteOpenCover :
    (simultaneousTwistedArithmeticStage hπ data H m 1 hj u hu).OpenCover :=
  (arithmeticFifthInitialOpenCover hπ data H m hj u hu).copy
    (ArithmeticChartLabel 2) A ι (Equiv.refl _) (fun i ↦ (E i).symm)
      (fun _ ↦ by rw [arithmeticOneFiniteAtlasChart]; rfl)

/-- Every point of the full global target remains covered by a finite chart. -/
theorem arithmeticOneFiniteAtlas_cover
    (z : simultaneousTwistedArithmeticStage hπ data H m 1 hj u hu) :
    ∃ i x, ι i x = z := (arithmeticOneFiniteOpenCover hπ data H k m hj u hu).exists_eq z

end FLT.Mazur.WeierstrassDividedDepth
