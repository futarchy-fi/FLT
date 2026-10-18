/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroDiagonalClosingUnion

/-!
# Chart restrictions of the actual diagonal closing comparisons

Both complete source closing unions embed into the independent target.
Their comparison maps preserve every point of both nodes, reflect equality,
and agree on the one full common terminal.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFifthAtlasChart arithmeticZeroFiniteInitialIso arithmeticZeroFiniteLastIso
  arithmeticZeroFiniteTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticZeroDiagonalAtlasChart hπ data H m hj u hu
local notation "D" => arithmeticZeroDiagonalState hπ data H 0 hj u hu

local notation "s" => PolygonArithmeticSimultaneous.State.last D m
local notation "t" => PolygonArithmeticSimultaneous.State.terminal D m
local notation "E" => arithmeticZeroFiniteAtlasIso hπ data H m m hj u hu
local notation "G" => simultaneousTwistedArithmeticIso hπ data H m 0 hj u hu

variable (b : Bool)
local notation "l" => Iso.hom (edgeInversion Q) ≫ leftBranchOpen Q (s b)
local notation "r" => punctureOpen t b
local notation "c" => ι (ArithmeticChartLabel.retained (Fin.mk 0 (Nat.zero_lt_succ 0)) b)
local notation "d" => ι ArithmeticChartLabel.terminal

local notation "U" => arithmeticZeroDiagonalClosingUnion hπ data H m hj u hu
local notation "J" => arithmeticZeroDiagonalClosingUnionIso hπ data H m hj u hu
local notation "V" => arithmeticZeroDiagonalPolygonClosingUnion hπ data H m hj u hu
local notation "K" => arithmeticZeroDiagonalClosingComparisonIso hπ data H m hj u hu

/-- The entire actual closing union maps into the independent diagonal polygon. -/
def arithmeticZeroDiagonalClosingUnionMap :
    (U b).toScheme ⟶ arithmeticZeroDiagonalPolygon hπ data H m hj u hu :=
  (K b).hom ≫ (V b).ι

local notation "f" => arithmeticZeroDiagonalClosingUnionMap hπ data H m hj u hu

instance arithmeticZeroDiagonalClosingUnionMap_isOpenImmersion : IsOpenImmersion (f b) := by
  unfold arithmeticZeroDiagonalClosingUnionMap
  infer_instance

/-- Every point of the complete retained chart has its prescribed target image. -/
@[reassoc] theorem arithmeticZeroDiagonalClosingUnionMap_retained :
    (pushout.inl l r ≫ (J b).hom) ≫ f b =
      arithmeticZeroDiagonalPolygonRetainedMap hπ data H m hj u hu b := by
  simp only [arithmeticZeroDiagonalClosingUnionMap, Category.assoc,
    arithmeticZeroDiagonalClosingComparisonIso_target,
    arithmeticZeroDiagonalClosingMap_retained]

/-- Every point of the complete terminal has its prescribed common target image. -/
@[reassoc] theorem arithmeticZeroDiagonalClosingUnionMap_terminal :
    (pushout.inr l r ≫ (J b).hom) ≫ f b =
      arithmeticZeroDiagonalPolygonTerminalChart hπ data H m hj u hu := by
  simp only [arithmeticZeroDiagonalClosingUnionMap, Category.assoc,
    arithmeticZeroDiagonalClosingComparisonIso_target,
    arithmeticZeroDiagonalClosingMap_terminal]

/-- The source closing comparison reflects equality on the whole open union. -/
theorem arithmeticZeroDiagonalClosingUnionMap_injective : Function.Injective (f b) :=
  (f b).isOpenEmbedding.injective

/-- Both full source terminal restrictions agree in the independent target. -/
theorem arithmeticZeroDiagonalClosingUnionMap_common_terminal :
    (pushout.inr ((edgeInversion Q).hom ≫ leftBranchOpen Q (s false))
        (punctureOpen t false) ≫ (J false).hom) ≫ f false =
      (pushout.inr ((edgeInversion Q).hom ≫ leftBranchOpen Q (s true))
        (punctureOpen t true) ≫ (J true).hom) ≫ f true := by
  rw [arithmeticZeroDiagonalClosingUnionMap_terminal,
    arithmeticZeroDiagonalClosingUnionMap_terminal]

end FLT.Mazur.WeierstrassDividedDepth
