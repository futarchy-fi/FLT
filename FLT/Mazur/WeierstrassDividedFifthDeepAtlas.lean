/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthDeepInputIdentification
public import FLT.Mazur.WeierstrassDividedFifthShallowJointGeometry
public import FLT.Mazur.WeierstrassDividedFourthOuterAtlasSystem

/-!
# The full fifth atlas at depths at least four

Install the last, predecessor, outer, farther, next earlier and terminal
factors together. The entire original initial opens and infinity stay covered.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthOuterAtlasChart arithmeticFifthDeepNodeIso arithmeticFifthDeepEarlierIso
  arithmeticFifthShallowLastOrientedIso arithmeticFifthShallowTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (hj₄ : 4 ≤ j)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "B" => arithmeticFourthOuterAtlasObject hπ data H m j hj u hu
local notation "κ" => arithmeticFourthOuterAtlasChart hπ data H m j hj u hu
local notation "I" => arithmeticFourthOuterAtlasIso hπ data H m j hj u hu
local notation "t" => fun v ↦ arithmeticFifthDeepSmoothing hπ data H j hj u hu v m

omit hj₄ in
/-- The complete fifth objects at all labels, retaining the whole initial and infinity charts. -/
def arithmeticFifthDeepAtlasObject : ArithmeticChartLabel (j + 1) → Scheme
  | .retained a b =>
      if a.val = j then PolygonSmoothing.chart Q τ
      else if a.val + 1 = j then PolygonSmoothing.chart Q (t .predecessor b)
      else if a.val + 2 = j then PolygonSmoothing.chart Q (t .outer b)
      else if a.val + 3 = j then PolygonSmoothing.chart Q (t .farther b)
      else if a.val + 4 = j then PolygonSmoothing.chart Q
        (arithmeticFifthDeepEarlierSmoothing hπ data H j hj u hu m b)
      else B (.retained a b)
  | .terminal => PolygonSmoothing.chart Q
      (arithmeticFifthShallowTerminalSmoothing hπ data H j hj u hu m)
  | i => B i

local notation "A" => arithmeticFifthDeepAtlasObject hπ data H m j hj u hu

/-- Each full fifth factor starts at its actual fourth source, in its original orientation. -/
def arithmeticFifthDeepAtlasCorrection (i : ArithmeticChartLabel (j + 1)) : B i ≅ A i :=
  match i with
  | .retained a b => by
      by_cases hl : a.val = j
      · exact eqToIso (congrArg (fun k : Fin (j + 1) ↦ B (.retained k b))
          (show a = ⟨j, by omega⟩ from Fin.ext hl)) ≪≫
          (arithmeticFourthOuterLastIdentification hπ data H m j hj u hu b).symm ≪≫
          arithmeticFifthShallowLastOrientedIso hπ data H m j hj u hu b ≪≫
          eqToIso (by simp only [arithmeticFifthDeepAtlasObject, hl, ↓reduceIte])
      · by_cases hp : a.val + 1 = j
        · exact (arithmeticFifthDeepInputIdentification
            hπ data H m j hj u hu hj₄ .predecessor a.val hp b).symm ≪≫
            arithmeticFifthDeepNodeIso hπ data H j hj u hu m .predecessor b ≪≫
            eqToIso (by simp only [arithmeticFifthDeepAtlasObject, hl, hp, ↓reduceIte])
        · by_cases ho : a.val + 2 = j
          · exact (arithmeticFifthDeepInputIdentification
              hπ data H m j hj u hu hj₄ .outer a.val ho b).symm ≪≫
              arithmeticFifthDeepNodeIso hπ data H j hj u hu m .outer b ≪≫
              eqToIso (by simp only [arithmeticFifthDeepAtlasObject, hl, hp, ho, ↓reduceIte])
          · by_cases hf : a.val + 3 = j
            · exact (arithmeticFifthDeepInputIdentification
                hπ data H m j hj u hu hj₄ .farther a.val hf b).symm ≪≫
                arithmeticFifthDeepNodeIso hπ data H j hj u hu m .farther b ≪≫
                eqToIso (by
                  simp only [arithmeticFifthDeepAtlasObject, hl, hp, ho, hf, ↓reduceIte])
            · by_cases he : a.val + 4 = j
              · exact (arithmeticFifthDeepEarlierInputIdentification
                  hπ data H m j hj u hu a.val he b).symm ≪≫
                  (twistedRetainedOrientation data H m b).symm ≪≫
                  arithmeticFifthDeepEarlierIso hπ data H j hj u hu m b ≪≫
                  eqToIso (by
                    simp only [arithmeticFifthDeepAtlasObject, hl, hp, ho, hf, he, ↓reduceIte])
              · exact eqToIso (by
                  simp only [arithmeticFifthDeepAtlasObject, hl, hp, ho, hf, he, ↓reduceIte])
  | .terminal => arithmeticFifthShallowTerminalIso hπ data H m j hj u hu
  | .initial _ => Iso.refl _
  | .infinity => Iso.refl _

attribute [local irreducible] arithmeticFifthDeepAtlasCorrection
local notation "E" => arithmeticFifthDeepAtlasCorrection hπ data H m j hj u hu hj₄

/-- The installed fifth chart includes into the full original global target. -/
def arithmeticFifthDeepAtlasChart (i : ArithmeticChartLabel (j + 1)) :
    A i ⟶ simultaneousTwistedArithmeticStage hπ data H m j hj u hu := (E i).inv ≫ κ i

instance arithmeticFifthDeepAtlasChart_isOpenImmersion (i : ArithmeticChartLabel (j + 1)) :
    IsOpenImmersion (arithmeticFifthDeepAtlasChart hπ data H m j hj u hu hj₄ i) := by
  unfold arithmeticFifthDeepAtlasChart
  infer_instance

/-- Every original full chart has its composed five-round comparison. -/
def arithmeticFifthDeepAtlasIso (i : ArithmeticChartLabel (j + 1)) :
    arithmeticLabeledAtlasObject hπ data H m (j + 1) hj i ≅ A i := I i ≪≫ E i

local notation "ι" => arithmeticFifthDeepAtlasChart hπ data H m j hj u hu hj₄

/-- The full installed correction recovers its exact fourth inclusion. -/
@[reassoc] theorem arithmeticFifthDeepAtlasCorrection_chart (i : ArithmeticChartLabel (j + 1)) :
    (E i).hom ≫ ι i = κ i := by
  rw [arithmeticFifthDeepAtlasChart, Iso.hom_inv_id_assoc]

/-- The original full inclusion is recovered by the composed five-round comparison. -/
@[reassoc] theorem arithmeticFifthDeepAtlasIso_chart (i : ArithmeticChartLabel (j + 1)) :
    arithmeticLabeledAtlasMap hπ data H m (j + 1) hj i ≫
        (simultaneousTwistedArithmeticIso hπ data H m j hj u hu).hom =
      (arithmeticFifthDeepAtlasIso hπ data H m j hj u hu hj₄ i).hom ≫ ι i := by
  rw [arithmeticFifthDeepAtlasIso, Iso.trans_hom, Category.assoc,
    arithmeticFifthDeepAtlasCorrection_chart]
  exact arithmeticFourthOuterAtlasIso_chart hπ data H m j hj u hu i

attribute [local irreducible] arithmeticFifthDeepAtlasChart

/-- The simultaneous fifth factors transport the entire original open cover. -/
def arithmeticFifthDeepOpenCover :
    (simultaneousTwistedArithmeticStage hπ data H m j hj u hu).OpenCover :=
  (arithmeticFourthOuterOpenCover hπ data H m j hj u hu).copy
    (ArithmeticChartLabel (j + 1)) A ι (Equiv.refl _) (fun i ↦ (E i).symm)
      (fun _ ↦ by rw [arithmeticFifthDeepAtlasChart]; rfl)

/-- Every point of the full global target belongs to an installed fifth chart. -/
theorem arithmeticFifthDeepAtlas_cover
    (z : simultaneousTwistedArithmeticStage hπ data H m j hj u hu) :
    ∃ i x, ι i x = z := (arithmeticFifthDeepOpenCover hπ data H m j hj u hu hj₄).exists_eq z

end FLT.Mazur.WeierstrassDividedDepth
