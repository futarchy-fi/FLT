/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOneDiagonalAtlas

/-!
# Full original initial-open transport at depth one

Compose the third, fourth, fifth and finite corrections on both the entire
node and the original polynomial open. Every intermediate smoothing is retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] arithmeticThirdInitialIso arithmeticFourthInitialIso
  arithmeticFifthInitialIso arithmeticOneFiniteInitialIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "M" => arithmeticInitialMobiusChart W H.a1_unit (π ^ 1) π m

/-- The entire depth-one initial node retains all corrections from its original smoothing. -/
def arithmeticOneFiniteInitialTotalNodeIso (k : ℕ) (b : Bool) :
    PolygonSmoothing.chart Q τ ≅ PolygonSmoothing.chart Q
      ((arithmeticOneFiniteState hπ data H hj u hu k).initial m b) :=
  arithmeticThirdEarlierIso hπ data H m 1 hj u hu b ≪≫
    arithmeticFourthInitialNodeIso hπ data H m 1 hj u hu b ≪≫
    arithmeticFifthInitialNodeIso hπ data H m 1 hj u hu b ≪≫
    arithmeticOneFiniteInitialNodeIso hπ data H k m hj u hu b

/-- The whole original polynomial initial open maps to its actual finite corrected open. -/
def arithmeticOneFiniteInitialTotalOpenIso (k : ℕ) (b : Bool) :
    Spec (.of (PolynomialNodeOpen (W.map (algebraMap R Q)) (algebraMap R Q (π ^ 1)))) ≅
      arithmeticOneFiniteInitialObject hπ data H k m hj u hu b :=
  arithmeticThirdInitialIso hπ data H m 1 hj u hu b ≪≫
    arithmeticFourthInitialIso hπ data H m 1 hj u hu b ≪≫
    arithmeticFifthInitialIso hπ data H m 1 hj u hu b ≪≫
    arithmeticOneFiniteInitialIso hπ data H k m hj u hu b

omit [IsBezout R] in
/-- The entire original open and full node comparisons commute on the original Mobius chart. -/
@[reassoc] theorem arithmeticOneFiniteInitialTotalOpenIso_nodeChart (k : ℕ) (b : Bool) :
    (arithmeticOneFiniteInitialTotalOpenIso hπ data H m hj u hu k b).hom ≫
      arithmeticOneFiniteInitialNodeChart hπ data H k m hj u hu b =
        M ≫ (arithmeticOneFiniteInitialTotalNodeIso hπ data H m hj u hu k b).hom := by
  simp only [arithmeticOneFiniteInitialTotalOpenIso, arithmeticOneFiniteInitialTotalNodeIso,
    Iso.trans_hom, Category.assoc, arithmeticOneFiniteInitialIso_nodeChart,
    arithmeticFifthInitialIso_nodeChart_assoc, arithmeticFourthInitialIso_nodeChart_assoc,
    arithmeticThirdInitialIso_nodeChart_assoc]

/-- The actual depth-one diagonal full node comparison starts on the original smoothing. -/
def arithmeticOneDiagonalInitialTotalNodeIso (b : Bool) :
    PolygonSmoothing.chart Q τ ≅ PolygonSmoothing.chart Q
      ((arithmeticOneDiagonalState hπ data H hj u hu).initial m b) :=
  arithmeticOneFiniteInitialTotalNodeIso hπ data H m hj u hu m b

/-- The original polynomial open maps to the actual depth-one diagonal initial open. -/
def arithmeticOneDiagonalInitialTotalOpenIso (b : Bool) :
    Spec (.of (PolynomialNodeOpen (W.map (algebraMap R Q)) (algebraMap R Q (π ^ 1)))) ≅
      arithmeticOneDiagonalAtlasObject hπ data H m hj u hu (.initial b) :=
  arithmeticOneFiniteInitialTotalOpenIso hπ data H m hj u hu m b

omit [IsBezout R] in
/-- The diagonal order keeps the same exact whole-open and entire-node square. -/
@[reassoc] theorem arithmeticOneDiagonalInitialTotalOpenIso_nodeChart (b : Bool) :
    (arithmeticOneDiagonalInitialTotalOpenIso hπ data H m hj u hu b).hom ≫
      arithmeticOneFiniteInitialNodeChart hπ data H m m hj u hu b =
        M ≫ (arithmeticOneDiagonalInitialTotalNodeIso hπ data H m hj u hu b).hom :=
  arithmeticOneFiniteInitialTotalOpenIso_nodeChart hπ data H m hj u hu m b

end FLT.Mazur.WeierstrassDividedDepth
