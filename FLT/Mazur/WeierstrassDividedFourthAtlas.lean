/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthGeometry
public import FLT.Mazur.WeierstrassDividedThirdEarlierGeometry

/-!
# Fourth full atlas with all available retained corrections

The last, predecessor, earlier retained pair and terminal carry their actual
full fourth factors. The depth-one initial charts retain their full third correction. Their fourth
correction and the further outer edges remain separate constructions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthLastOrientedIso arithmeticFourthPrecedingIso
  arithmeticFourthEarlierIso arithmeticFourthTerminalIso
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

/-- Each changed retained label keeps its exact fourth smoothing. -/
def arithmeticFourthAtlasObject : ArithmeticChartLabel (j + 1) → Scheme
  | .terminal => PolygonSmoothing.chart Q
      (arithmeticFourthTerminalSmoothing hπ data H j hj u hu m)
  | .retained a b => if a.val + 1 = j then
      PolygonSmoothing.chart Q (arithmeticFourthPrecedingSmoothing hπ data H j hj u hu m b)
      else if a.val + 2 = j then
        PolygonSmoothing.chart Q (arithmeticFourthEarlierSmoothing hπ data H j hj u hu m b)
      else B (.retained a b)
  | .initial b => B (.initial b)
  | .infinity => B .infinity

local notation "A" => arithmeticFourthAtlasObject hπ data H m j hj u hu

/-- Install each full node correction only at the retained label where it belongs. -/
def arithmeticFourthAtlasCorrection (i : ArithmeticChartLabel (j + 1)) : B i ≅ A i :=
  match i with
  | .terminal => arithmeticFourthTerminalIso hπ data H m j hj u hu
  | .retained a b => by
      by_cases hp : a.val + 1 = j
      · exact (arithmeticThirdPrecedingIdentification
          hπ data H m j hj u hu a.val hp b).symm ≪≫
          arithmeticFourthPrecedingIso hπ data H m j hj u hu b ≪≫
          eqToIso (by simp only [arithmeticFourthAtlasObject, hp, ↓reduceIte])
      · by_cases he : a.val + 2 = j
        · exact (arithmeticThirdEarlierIdentification hπ data H m j hj u hu a.val he b).symm ≪≫
            arithmeticFourthEarlierIso hπ data H m j hj u hu b ≪≫
            eqToIso (by simp only [arithmeticFourthAtlasObject, hp, he, ↓reduceIte])
        · exact (if hl : a.val = j then
            (eqToIso (congrArg (fun i : Fin (j + 1) ↦ B (.retained i b))
              (show a = ⟨j, by omega⟩ from Fin.ext hl)) ≪≫
              (arithmeticThirdLastIdentification hπ data H m j hj u hu b).symm) ≪≫
              arithmeticFourthLastOrientedIso hπ data H m j hj u hu b ≪≫
              arithmeticThirdLastIdentification hπ data H m j hj u hu b ≪≫
              eqToIso (congrArg (fun i : Fin (j + 1) ↦ B (.retained i b))
                (show a = ⟨j, by omega⟩ from Fin.ext hl).symm)
            else Iso.refl _) ≪≫
            eqToIso (by simp only [arithmeticFourthAtlasObject, hp, he, ↓reduceIte])
  | .initial _ => Iso.refl _
  | .infinity => Iso.refl _

attribute [local irreducible] arithmeticFourthAtlasCorrection
local notation "E" => arithmeticFourthAtlasCorrection hπ data H m j hj u hu

/-- The actual corrected full chart inclusion in the global target. -/
def arithmeticFourthAtlasChart (i : ArithmeticChartLabel (j + 1)) :
    A i ⟶ simultaneousTwistedArithmeticStage hπ data H m j hj u hu :=
  (E i).inv ≫ κ i

instance arithmeticFourthAtlasChart_isOpenImmersion (i : ArithmeticChartLabel (j + 1)) :
    IsOpenImmersion (arithmeticFourthAtlasChart hπ data H m j hj u hu i) := by
  unfold arithmeticFourthAtlasChart
  infer_instance

/-- Every original full chart has its composed four-round comparison. -/
def arithmeticFourthAtlasIso (i : ArithmeticChartLabel (j + 1)) :
    arithmeticLabeledAtlasObject hπ data H m (j + 1) hj i ≅ A i := I i ≪≫ E i

local notation "ι" => arithmeticFourthAtlasChart hπ data H m j hj u hu

/-- The correction recovers its actual third-atlas inclusion. -/
@[reassoc] theorem arithmeticFourthAtlasCorrection_chart (i : ArithmeticChartLabel (j + 1)) :
    (E i).hom ≫ ι i = κ i := by
  rw [arithmeticFourthAtlasChart, Iso.hom_inv_id_assoc]

/-- The original full chart inclusion is recovered by the four constructed comparisons. -/
@[reassoc] theorem arithmeticFourthAtlasIso_chart (i : ArithmeticChartLabel (j + 1)) :
    arithmeticLabeledAtlasMap hπ data H m (j + 1) hj i ≫ (G).hom =
      (arithmeticFourthAtlasIso hπ data H m j hj u hu i).hom ≫ ι i := by
  rw [arithmeticFourthAtlasIso, Iso.trans_hom, Category.assoc,
    arithmeticFourthAtlasCorrection_chart]
  exact arithmeticThirdInitialAtlasIso_chart hπ data H m j hj u hu i

attribute [local irreducible] arithmeticFourthAtlasChart arithmeticThirdInitialAtlasChart

/-- Transport the complete original cover through the full fourth node factors. -/
def arithmeticFourthOpenCover :
    (simultaneousTwistedArithmeticStage hπ data H m j hj u hu).OpenCover :=
  (arithmeticThirdInitialOpenCover hπ data H m j hj u hu).copy
    (ArithmeticChartLabel (j + 1)) A ι (Equiv.refl _) (fun i ↦ (E i).symm)
      (fun _ ↦ by rw [arithmeticFourthAtlasChart]; rfl)

/-- The installed fourth charts cover the entire target, including its original infinity. -/
theorem arithmeticFourthAtlas_cover
    (z : simultaneousTwistedArithmeticStage hπ data H m j hj u hu) :
    ∃ i x, ι i x = z := (arithmeticFourthOpenCover hπ data H m j hj u hu).exists_eq z

end FLT.Mazur.WeierstrassDividedDepth
