/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInitialTransport

/-!
# Full node transport for the original depth-zero initial open

Compose the actual node factors, keeping every changed smoothing. The original
open comparison and the full node comparison form a commuting square.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFirstInitialIso arithmeticZeroSecondInitialIso arithmeticZeroThirdInitialIso
  arithmeticZeroFourthInitialIso arithmeticZeroFifthInitialIso arithmeticZeroFiniteInitialIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "M" => arithmeticInitialMobiusChart W H.a1_unit (π ^ 1) π m

/-- The complete second initial node factor starts on the original smoothing. -/
def arithmeticZeroSecondInitialTotalNodeIso (b : Bool) :
    PolygonSmoothing.chart Q τ ≅ PolygonSmoothing.chart Q
      (arithmeticZeroSecondInitialSmoothing hπ data H 0 hj u hu m b) :=
  arithmeticZeroFirstInitialNodeIso hπ data H m 0 hj u hu b ≪≫
    arithmeticZeroSecondInitialNodeIso hπ data H m 0 hj u hu b

/-- The complete third initial node factor starts on the original smoothing. -/
def arithmeticZeroThirdInitialTotalNodeIso (b : Bool) :
    PolygonSmoothing.chart Q τ ≅ PolygonSmoothing.chart Q
      (arithmeticZeroThirdInitialSmoothing hπ data H 0 hj u hu m b) :=
  arithmeticZeroSecondInitialTotalNodeIso hπ data H m hj u hu b ≪≫
    arithmeticZeroThirdInitialNodeIso hπ data H m 0 hj u hu b

/-- The complete fourth initial node factor starts on the original smoothing. -/
def arithmeticZeroFourthInitialTotalNodeIso (b : Bool) :
    PolygonSmoothing.chart Q τ ≅ PolygonSmoothing.chart Q
      (arithmeticZeroFourthInitialSmoothing hπ data H 0 hj u hu m b) :=
  arithmeticZeroThirdInitialTotalNodeIso hπ data H m hj u hu b ≪≫
    arithmeticZeroFourthInitialNodeIso hπ data H m 0 hj u hu b

/-- The complete fifth initial node factor starts on the original smoothing. -/
def arithmeticZeroFifthInitialTotalNodeIso (b : Bool) :
    PolygonSmoothing.chart Q τ ≅ PolygonSmoothing.chart Q
      (arithmeticZeroFifthInitialSmoothing hπ data H 0 hj u hu m b) :=
  arithmeticZeroFourthInitialTotalNodeIso hπ data H m hj u hu b ≪≫
    arithmeticZeroFifthInitialNodeIso hπ data H m 0 hj u hu b

/-- The first initial open square uses the entire original chart comparison. -/
@[reassoc] theorem arithmeticZeroFirstAtlasIso_initial_nodeChart (b : Bool) :
    (arithmeticZeroFirstAtlasIso hπ data H m hj u hu (.initial b)).hom ≫
      arithmeticZeroFirstInitialNodeChart hπ data H m 0 hj u hu b =
        M ≫ (arithmeticZeroFirstInitialNodeIso hπ data H m 0 hj u hu b).hom := by
  rw [arithmeticZeroFirstAtlasIso_initial, arithmeticZeroFirstInitialIso_nodeChart]

/-- The complete second open square retains every earlier node factor. -/
@[reassoc] theorem arithmeticZeroSecondAtlasIso_initial_nodeChart (b : Bool) :
    (arithmeticZeroSecondAtlasIso hπ data H m hj u hu (.initial b)).hom ≫
      arithmeticZeroSecondInitialNodeChart hπ data H m 0 hj u hu b =
        M ≫ (arithmeticZeroSecondInitialTotalNodeIso hπ data H m hj u hu b).hom := by
  simp only [arithmeticZeroSecondAtlasIso, arithmeticZeroSecondAtlasCorrection,
    arithmeticZeroSecondInitialTotalNodeIso, Iso.trans_hom, Category.assoc,
    arithmeticZeroSecondInitialIso_nodeChart]
  rw [← Category.assoc, arithmeticZeroFirstAtlasIso_initial_nodeChart, Category.assoc]

/-- The complete third open square retains every earlier node factor. -/
@[reassoc] theorem arithmeticZeroThirdAtlasIso_initial_nodeChart (b : Bool) :
    (arithmeticZeroThirdAtlasIso hπ data H m hj u hu (.initial b)).hom ≫
      arithmeticZeroThirdInitialNodeChart hπ data H m 0 hj u hu b =
        M ≫ (arithmeticZeroThirdInitialTotalNodeIso hπ data H m hj u hu b).hom := by
  simp only [arithmeticZeroThirdAtlasIso, arithmeticZeroThirdAtlasCorrection,
    arithmeticZeroThirdInitialTotalNodeIso, Iso.trans_hom, Category.assoc,
    arithmeticZeroThirdInitialIso_nodeChart]
  rw [← Category.assoc, arithmeticZeroSecondAtlasIso_initial_nodeChart, Category.assoc]

/-- The complete fourth open square retains every earlier node factor. -/
@[reassoc] theorem arithmeticZeroFourthAtlasIso_initial_nodeChart (b : Bool) :
    (arithmeticZeroFourthAtlasIso hπ data H m hj u hu (.initial b)).hom ≫
      arithmeticZeroFourthInitialNodeChart hπ data H m 0 hj u hu b =
        M ≫ (arithmeticZeroFourthInitialTotalNodeIso hπ data H m hj u hu b).hom := by
  simp only [arithmeticZeroFourthAtlasIso, arithmeticZeroFourthAtlasCorrection,
    arithmeticZeroFourthInitialTotalNodeIso, Iso.trans_hom, Category.assoc,
    arithmeticZeroFourthInitialIso_nodeChart]
  rw [← Category.assoc, arithmeticZeroThirdAtlasIso_initial_nodeChart, Category.assoc]

/-- The complete fifth open square retains every earlier node factor. -/
@[reassoc] theorem arithmeticZeroFifthAtlasIso_initial_nodeChart (b : Bool) :
    (arithmeticZeroFifthAtlasIso hπ data H m hj u hu (.initial b)).hom ≫
      arithmeticZeroFifthInitialNodeChart hπ data H m 0 hj u hu b =
        M ≫ (arithmeticZeroFifthInitialTotalNodeIso hπ data H m hj u hu b).hom := by
  simp only [arithmeticZeroFifthAtlasIso, arithmeticZeroFifthAtlasCorrection,
    arithmeticZeroFifthInitialTotalNodeIso, Iso.trans_hom, Category.assoc,
    arithmeticZeroFifthInitialIso_nodeChart]
  rw [← Category.assoc, arithmeticZeroFourthAtlasIso_initial_nodeChart, Category.assoc]

/-- All finite initial node corrections start at the original full smoothing. -/
def arithmeticZeroFiniteInitialTotalNodeIso (k : ℕ) (b : Bool) :
    PolygonSmoothing.chart Q τ ≅ PolygonSmoothing.chart Q
      ((arithmeticZeroFiniteState hπ data H 0 hj u hu k).initial m b) :=
  arithmeticZeroFifthInitialTotalNodeIso hπ data H m hj u hu b ≪≫
    arithmeticZeroFiniteInitialNodeIso hπ data H k m 0 hj u hu b

/-- The full finite open square remembers the original chart on the whole open. -/
@[reassoc] theorem arithmeticZeroFiniteAtlasIso_initial_nodeChart (k : ℕ) (b : Bool) :
    (arithmeticZeroFiniteAtlasIso hπ data H k m hj u hu (.initial b)).hom ≫
      arithmeticZeroFiniteInitialNodeChart hπ data H k m 0 hj u hu b =
        M ≫ (arithmeticZeroFiniteInitialTotalNodeIso hπ data H m hj u hu k b).hom := by
  simp only [arithmeticZeroFiniteAtlasIso, arithmeticZeroFiniteAtlasCorrection,
    arithmeticZeroFiniteInitialTotalNodeIso, Iso.trans_hom, Category.assoc,
    arithmeticZeroFiniteInitialIso_nodeChart]
  rw [← Category.assoc, arithmeticZeroFifthAtlasIso_initial_nodeChart, Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth
