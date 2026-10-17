/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThirdGeometry

/-!
# Third full atlas with all available retained corrections

The last, predecessor, earlier retained pair and terminal carry their actual
full third factors. Initial charts are retained unchanged here; their extra
correction at depth one is a separate construction, not an asserted edge equation.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticThirdLastOrientedIso arithmeticThirdPrecedingIso
  arithmeticThirdEarlierOrientedIso arithmeticThirdTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "B" => arithmeticSecondJointAtlasObject hπ data H m j hj u hu
local notation "κ" => arithmeticSecondJointAtlasChart hπ data H m j hj u hu
local notation "I" => arithmeticSecondJointAtlasIso hπ data H m j hj u hu
local notation "G" => simultaneousTwistedArithmeticIso hπ data H m j hj u hu

/-- Each changed retained label keeps its exact third smoothing. -/
def arithmeticThirdAtlasObject : ArithmeticChartLabel (j + 1) → Scheme
  | .terminal => PolygonSmoothing.chart Q
      (arithmeticThirdTerminalSmoothing hπ data H j hj u hu m)
  | .retained a b => if a.val + 1 = j then
      PolygonSmoothing.chart Q (arithmeticThirdPrecedingSmoothing hπ data H j hj u hu m b)
      else if a.val + 2 = j then
        PolygonSmoothing.chart Q (arithmeticThirdEarlierSmoothing hπ data H j hj u hu m b)
      else B (.retained a b)
  | .initial b => B (.initial b)
  | .infinity => B .infinity

local notation "A" => arithmeticThirdAtlasObject hπ data H m j hj u hu

/-- Install each full node correction only at the retained label where it belongs. -/
def arithmeticThirdAtlasCorrection (i : ArithmeticChartLabel (j + 1)) : B i ≅ A i :=
  match i with
  | .terminal => arithmeticThirdTerminalIso hπ data H m j hj u hu
  | .retained a b => by
      by_cases hp : a.val + 1 = j
      · exact (arithmeticSecondJointPrecedingIdentification
          hπ data H m j hj u hu a.val hp b).symm ≪≫
          arithmeticThirdPrecedingIso hπ data H m j hj u hu b ≪≫
          eqToIso (by simp only [arithmeticThirdAtlasObject, hp, ↓reduceIte])
      · let N := arithmeticSecondJointUnchangedIdentification hπ data H j hj u hu m a hp b
        by_cases he : a.val + 2 = j
        · exact N.symm ≪≫ arithmeticThirdEarlierOrientedIso hπ data H m j hj u hu b ≪≫
            eqToIso (by simp only [arithmeticThirdAtlasObject, hp, he, ↓reduceIte])
        · exact (if a.val = j then
            N.symm ≪≫ arithmeticThirdLastOrientedIso hπ data H m j hj u hu b ≪≫ N
            else Iso.refl _) ≪≫
            eqToIso (by simp only [arithmeticThirdAtlasObject, hp, he, ↓reduceIte])
  | .initial _ => Iso.refl _
  | .infinity => Iso.refl _

attribute [local irreducible] arithmeticThirdAtlasCorrection
local notation "E" => arithmeticThirdAtlasCorrection hπ data H m j hj u hu

/-- The actual corrected full chart inclusion in the global target. -/
def arithmeticThirdAtlasChart (i : ArithmeticChartLabel (j + 1)) :
    A i ⟶ simultaneousTwistedArithmeticStage hπ data H m j hj u hu :=
  (E i).inv ≫ κ i

instance arithmeticThirdAtlasChart_isOpenImmersion (i : ArithmeticChartLabel (j + 1)) :
    IsOpenImmersion (arithmeticThirdAtlasChart hπ data H m j hj u hu i) := by
  unfold arithmeticThirdAtlasChart
  infer_instance

/-- Every original full chart has its composed three-round comparison. -/
def arithmeticThirdAtlasIso (i : ArithmeticChartLabel (j + 1)) :
    arithmeticLabeledAtlasObject hπ data H m (j + 1) hj i ≅ A i := I i ≪≫ E i

local notation "ι" => arithmeticThirdAtlasChart hπ data H m j hj u hu

/-- The correction recovers its actual second-atlas inclusion. -/
@[reassoc] theorem arithmeticThirdAtlasCorrection_chart (i : ArithmeticChartLabel (j + 1)) :
    (E i).hom ≫ ι i = κ i := by
  rw [arithmeticThirdAtlasChart, Iso.hom_inv_id_assoc]

/-- The original full chart inclusion is recovered by the three constructed comparisons. -/
@[reassoc] theorem arithmeticThirdAtlasIso_chart (i : ArithmeticChartLabel (j + 1)) :
    arithmeticLabeledAtlasMap hπ data H m (j + 1) hj i ≫ (G).hom =
      (arithmeticThirdAtlasIso hπ data H m j hj u hu i).hom ≫ ι i := by
  rw [arithmeticThirdAtlasIso, Iso.trans_hom, Category.assoc,
    arithmeticThirdAtlasCorrection_chart]
  exact arithmeticSecondJointAtlasIso_chart hπ data H m j hj u hu i

attribute [local irreducible] arithmeticThirdAtlasChart arithmeticSecondJointAtlasChart

/-- Transport the complete original cover through the full third node factors. -/
def arithmeticThirdOpenCover :
    (simultaneousTwistedArithmeticStage hπ data H m j hj u hu).OpenCover :=
  (arithmeticSecondJointOpenCover hπ data H m j hj u hu).copy
    (ArithmeticChartLabel (j + 1)) A ι (Equiv.refl _) (fun i ↦ (E i).symm)
      (fun _ ↦ by rw [arithmeticThirdAtlasChart]; rfl)

/-- The installed third charts cover the entire target, including its original infinity. -/
theorem arithmeticThirdAtlas_cover
    (z : simultaneousTwistedArithmeticStage hπ data H m j hj u hu) :
    ∃ i x, ι i x = z := (arithmeticThirdOpenCover hπ data H m j hj u hu).exists_eq z

end FLT.Mazur.WeierstrassDividedDepth
