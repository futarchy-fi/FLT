/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthFartherInputIdentification
public import FLT.Mazur.WeierstrassDividedFifthShallowJointGeometry
public import FLT.Mazur.WeierstrassDividedFourthOuterAtlasSystem
public import FLT.Mazur.WeierstrassDividedFourthFartherInitial
public import FLT.Mazur.WeierstrassDividedFifthFartherGeometry

/-!
# The full fifth atlas at depth three

Install the last, predecessor, outer, specialized farther and terminal factors
together with both corrected original initial opens. Infinity stays covered.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthOuterAtlasChart arithmeticFifthDeepNodeIso arithmeticFifthFartherNeighborIso
  arithmeticFifthFartherIso
  arithmeticFifthShallowLastOrientedIso arithmeticFifthShallowTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (ha : 3 = j)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "B" => arithmeticFourthOuterAtlasObject hπ data H m j hj u hu
local notation "κ" => arithmeticFourthOuterAtlasChart hπ data H m j hj u hu
local notation "I" => arithmeticFourthOuterAtlasIso hπ data H m j hj u hu
local notation "t" => fun v ↦ arithmeticFifthDeepSmoothing hπ data H j hj u hu v m

omit ha in
/-- The complete fifth objects at all labels, retaining the whole initial and infinity charts. -/
def arithmeticFifthFartherAtlasObject : ArithmeticChartLabel (j + 1) → Scheme
  | .retained a b =>
      if a.val = j then PolygonSmoothing.chart Q τ
      else if a.val + 1 = j then PolygonSmoothing.chart Q (t .predecessor b)
      else if a.val + 2 = j then PolygonSmoothing.chart Q (t .outer b)
      else if a.val + 3 = j then PolygonSmoothing.chart Q
        (arithmeticFifthFartherNeighborSmoothing hπ data H j hj u hu m b)
      else B (.retained a b)
  | .terminal => PolygonSmoothing.chart Q
      (arithmeticFifthShallowTerminalSmoothing hπ data H j hj u hu m)
  | .initial b => arithmeticFifthFartherObject hπ data H m j hj u hu b
  | .infinity => B .infinity

local notation "A" => arithmeticFifthFartherAtlasObject hπ data H m j hj u hu

/-- Each full fifth factor starts at its actual fourth source, in its original orientation. -/
def arithmeticFifthFartherAtlasCorrection (i : ArithmeticChartLabel (j + 1)) : B i ≅ A i :=
  match i with
  | .retained a b => by
      by_cases hl : a.val = j
      · exact eqToIso (congrArg (fun k : Fin (j + 1) ↦ B (.retained k b))
          (show a = ⟨j, by omega⟩ from Fin.ext hl)) ≪≫
          (arithmeticFourthOuterLastIdentification hπ data H m j hj u hu b).symm ≪≫
          arithmeticFifthShallowLastOrientedIso hπ data H m j hj u hu b ≪≫
          eqToIso (by simp only [arithmeticFifthFartherAtlasObject, hl, ↓reduceIte])
      · by_cases hp : a.val + 1 = j
        · exact (arithmeticFifthFartherInputIdentification
            hπ data H m j hj u hu (by omega) .predecessor a.val hp b).symm ≪≫
            arithmeticFifthDeepNodeIso hπ data H j hj u hu m .predecessor b ≪≫
            eqToIso (by simp only [arithmeticFifthFartherAtlasObject, hl, hp, ↓reduceIte])
        · by_cases ho : a.val + 2 = j
          · exact (arithmeticFifthFartherInputIdentification
              hπ data H m j hj u hu (by omega) .outer a.val ho b).symm ≪≫
              arithmeticFifthDeepNodeIso hπ data H j hj u hu m .outer b ≪≫
              eqToIso (by simp only [arithmeticFifthFartherAtlasObject, hl, hp, ho, ↓reduceIte])
          · by_cases hf : a.val + 3 = j
            · exact (arithmeticFourthFartherIdentification
                hπ data H m j hj u hu a.val hf b).symm ≪≫
                arithmeticFifthFartherNeighborIso hπ data H m j hj u hu b ≪≫
                eqToIso (by
                  simp only [arithmeticFifthFartherAtlasObject, hl, hp, ho, hf, ↓reduceIte])
            · exact eqToIso (by
                simp only [arithmeticFifthFartherAtlasObject, hl, hp, ho, hf, ↓reduceIte])
  | .terminal => arithmeticFifthShallowTerminalIso hπ data H m j hj u hu
  | .initial b =>
      (arithmeticFourthOuterInitialThreeIdentification hπ data H m j hj u hu ha b).symm ≪≫
        arithmeticFifthFartherIso hπ data H m j hj u hu b
  | .infinity => Iso.refl _

attribute [local irreducible] arithmeticFifthFartherAtlasCorrection
local notation "E" => arithmeticFifthFartherAtlasCorrection hπ data H m j hj u hu ha

/-- The installed fifth chart includes into the full original global target. -/
def arithmeticFifthFartherAtlasChart (i : ArithmeticChartLabel (j + 1)) :
    A i ⟶ simultaneousTwistedArithmeticStage hπ data H m j hj u hu := (E i).inv ≫ κ i

instance arithmeticFifthFartherAtlasChart_isOpenImmersion (i : ArithmeticChartLabel (j + 1)) :
    IsOpenImmersion (arithmeticFifthFartherAtlasChart hπ data H m j hj u hu ha i) := by
  unfold arithmeticFifthFartherAtlasChart
  infer_instance

/-- Every original full chart has its composed five-round comparison. -/
def arithmeticFifthFartherAtlasIso (i : ArithmeticChartLabel (j + 1)) :
    arithmeticLabeledAtlasObject hπ data H m (j + 1) hj i ≅ A i := I i ≪≫ E i

local notation "ι" => arithmeticFifthFartherAtlasChart hπ data H m j hj u hu ha

/-- The full installed correction recovers its exact fourth inclusion. -/
@[reassoc] theorem arithmeticFifthFartherAtlasCorrection_chart (i : ArithmeticChartLabel (j + 1)) :
    (E i).hom ≫ ι i = κ i := by
  rw [arithmeticFifthFartherAtlasChart, Iso.hom_inv_id_assoc]

/-- The original full inclusion is recovered by the composed five-round comparison. -/
@[reassoc] theorem arithmeticFifthFartherAtlasIso_chart (i : ArithmeticChartLabel (j + 1)) :
    arithmeticLabeledAtlasMap hπ data H m (j + 1) hj i ≫
        (simultaneousTwistedArithmeticIso hπ data H m j hj u hu).hom =
      (arithmeticFifthFartherAtlasIso hπ data H m j hj u hu ha i).hom ≫ ι i := by
  rw [arithmeticFifthFartherAtlasIso, Iso.trans_hom, Category.assoc,
    arithmeticFifthFartherAtlasCorrection_chart]
  exact arithmeticFourthOuterAtlasIso_chart hπ data H m j hj u hu i

attribute [local irreducible] arithmeticFifthFartherAtlasChart

/-- The simultaneous fifth factors transport the entire original open cover. -/
def arithmeticFifthFartherOpenCover :
    (simultaneousTwistedArithmeticStage hπ data H m j hj u hu).OpenCover :=
  (arithmeticFourthOuterOpenCover hπ data H m j hj u hu).copy
    (ArithmeticChartLabel (j + 1)) A ι (Equiv.refl _) (fun i ↦ (E i).symm)
      (fun _ ↦ by rw [arithmeticFifthFartherAtlasChart]; rfl)

/-- Every point of the full global target belongs to an installed fifth chart. -/
theorem arithmeticFifthFartherAtlas_cover
    (z : simultaneousTwistedArithmeticStage hπ data H m j hj u hu) :
    ∃ i x, ι i x = z := (arithmeticFifthFartherOpenCover hπ data H m j hj u hu ha).exists_eq z

end FLT.Mazur.WeierstrassDividedDepth
