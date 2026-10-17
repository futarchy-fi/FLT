/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthInitialAtlas
public import FLT.Mazur.WeierstrassDividedFourthOuterGeometry
public import FLT.Mazur.WeierstrassDividedThirdEarlierAdjacent

/-!
# Install the simultaneous fourth factors at the earlier retained labels

The earlier factor replaces its generic correction from the actual third
smoothing. The farther factor starts in the original oriented normalized chart.
All other labels retain their complete fourth initial atlas factors.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthOuterIso arithmeticFourthFartherIso
  arithmeticFourthInitialAtlasCorrection
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "B" => arithmeticThirdInitialAtlasObject hπ data H m j hj u hu
local notation "κ" => arithmeticThirdInitialAtlasChart hπ data H m j hj u hu
local notation "I" => arithmeticThirdInitialAtlasIso hπ data H m j hj u hu
local notation "G" => simultaneousTwistedArithmeticIso hπ data H m j hj u hu

/-- Replace the two actual retained labels and keep every other fourth chart. -/
def arithmeticFourthOuterAtlasObject : ArithmeticChartLabel (j + 1) → Scheme
  | .retained a b => if a.val + 2 = j then PolygonSmoothing.chart Q
      (arithmeticFourthOuterSmoothing hπ data H j hj u hu m b)
      else if a.val + 3 = j then PolygonSmoothing.chart Q
        (arithmeticFourthFartherSmoothing hπ data H j hj u hu m b)
      else arithmeticFourthInitialAtlasObject hπ data H m j hj u hu (.retained a b)
  | i => arithmeticFourthInitialAtlasObject hπ data H m j hj u hu i

local notation "A" => arithmeticFourthOuterAtlasObject hπ data H m j hj u hu
local notation "E₄" => arithmeticFourthInitialAtlasCorrection hπ data H m j hj u hu

/-- Both new factors start from the exact third sources at their actual labels. -/
def arithmeticFourthOuterAtlasCorrection (i : ArithmeticChartLabel (j + 1)) : B i ≅ A i :=
  match i with
  | .retained a b => by
      by_cases he : a.val + 2 = j
      · exact (arithmeticThirdEarlierIdentification
          hπ data H m j hj u hu a.val he b).symm ≪≫
          arithmeticFourthOuterIso hπ data H j hj u hu m b ≪≫
          eqToIso (by simp only [arithmeticFourthOuterAtlasObject, he, ↓reduceIte])
      · by_cases hf : a.val + 3 = j
        · exact (arithmeticThirdUnchangedIdentification
            hπ data H m j hj u hu a (by omega) b).symm ≪≫
            (twistedRetainedOrientation data H m b).symm ≪≫
            arithmeticFourthFartherIso hπ data H j hj u hu m b ≪≫
            eqToIso (by simp only [arithmeticFourthOuterAtlasObject, he, hf, ↓reduceIte])
        · exact E₄ (.retained a b) ≪≫
            eqToIso (by simp only [arithmeticFourthOuterAtlasObject, he, hf, ↓reduceIte])
  | .initial b => E₄ (.initial b)
  | .terminal => E₄ .terminal
  | .infinity => E₄ .infinity

attribute [local irreducible] arithmeticFourthOuterAtlasCorrection
local notation "E" => arithmeticFourthOuterAtlasCorrection hπ data H m j hj u hu

/-- The actual corrected full chart inclusion in the global target. -/
def arithmeticFourthOuterAtlasChart (i : ArithmeticChartLabel (j + 1)) :
    A i ⟶ simultaneousTwistedArithmeticStage hπ data H m j hj u hu :=
  (E i).inv ≫ κ i

instance arithmeticFourthOuterAtlasChart_isOpenImmersion (i : ArithmeticChartLabel (j + 1)) :
    IsOpenImmersion (arithmeticFourthOuterAtlasChart hπ data H m j hj u hu i) := by
  unfold arithmeticFourthOuterAtlasChart
  infer_instance

/-- Every original full chart has its composed four-round outer comparison. -/
def arithmeticFourthOuterAtlasIso (i : ArithmeticChartLabel (j + 1)) :
    arithmeticLabeledAtlasObject hπ data H m (j + 1) hj i ≅ A i := I i ≪≫ E i

local notation "ι" => arithmeticFourthOuterAtlasChart hπ data H m j hj u hu

/-- The correction recovers its actual third-atlas inclusion. -/
@[reassoc] theorem arithmeticFourthOuterAtlasCorrection_chart (i : ArithmeticChartLabel (j + 1)) :
    (E i).hom ≫ ι i = κ i := by
  rw [arithmeticFourthOuterAtlasChart, Iso.hom_inv_id_assoc]

/-- The original full chart inclusion is recovered by the four constructed comparisons. -/
@[reassoc] theorem arithmeticFourthOuterAtlasIso_chart (i : ArithmeticChartLabel (j + 1)) :
    arithmeticLabeledAtlasMap hπ data H m (j + 1) hj i ≫ (G).hom =
      (arithmeticFourthOuterAtlasIso hπ data H m j hj u hu i).hom ≫ ι i := by
  rw [arithmeticFourthOuterAtlasIso, Iso.trans_hom, Category.assoc,
    arithmeticFourthOuterAtlasCorrection_chart]
  exact arithmeticThirdInitialAtlasIso_chart hπ data H m j hj u hu i

attribute [local irreducible] arithmeticFourthOuterAtlasChart arithmeticThirdInitialAtlasChart

/-- Transport the complete original cover through the full fourth outer factors. -/
def arithmeticFourthOuterOpenCover :
    (simultaneousTwistedArithmeticStage hπ data H m j hj u hu).OpenCover :=
  (arithmeticThirdInitialOpenCover hπ data H m j hj u hu).copy
    (ArithmeticChartLabel (j + 1)) A ι (Equiv.refl _) (fun i ↦ (E i).symm)
      (fun _ ↦ by rw [arithmeticFourthOuterAtlasChart]; rfl)

/-- The installed fourth charts cover the entire target, including its original infinity. -/
theorem arithmeticFourthOuterAtlas_cover
    (z : simultaneousTwistedArithmeticStage hπ data H m j hj u hu) :
    ∃ i x, ι i x = z := (arithmeticFourthOuterOpenCover hπ data H m j hj u hu).exists_eq z

end FLT.Mazur.WeierstrassDividedDepth
