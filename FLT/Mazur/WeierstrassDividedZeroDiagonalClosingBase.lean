/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroDiagonalClosingRestriction
public import FLT.Mazur.WeierstrassDividedZeroClosingAtlasBase

/-!
# Full diagonal closing comparisons preserve the original arithmetic base

Both entire source node charts retain their actual coefficient projection.
The two whole closing unions therefore map over the original global base.
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

local notation "q" => arithmeticZeroDiagonalSourceToBase hπ data H m hj u hu
local notation "p" => arithmeticZeroDiagonalPolygonToBase hπ data H m hj u hu
local notation "U" => arithmeticZeroDiagonalClosingUnion hπ data H m hj u hu
local notation "J" => arithmeticZeroDiagonalClosingUnionIso hπ data H m hj u hu
local notation "F" => arithmeticZeroDiagonalClosingUnionMap hπ data H m hj u hu

/-- The full diagonal retained source has the original global quotient coefficient map. -/
@[reassoc] theorem arithmeticZeroDiagonalAtlas_retained_base (b : Bool) :
    ι (.retained ⟨0, by omega⟩ b) ≫ q = chartStructure Q (s b) :=
  arithmeticZeroFiniteAtlas_retained_base hπ data H m hj u hu m b

/-- The full common terminal source has the original global quotient coefficient map. -/
@[reassoc] theorem arithmeticZeroDiagonalAtlas_terminal_base :
    ι .terminal ≫ q = chartStructure Q t :=
  arithmeticZeroFiniteAtlas_terminal_base hπ data H m hj u hu m

omit [IsBezout R] in
/-- The complete independent terminal chart retains the same full quotient coefficients. -/
@[reassoc] theorem arithmeticZeroDiagonalPolygonTerminalChart_base :
    arithmeticZeroDiagonalPolygonTerminalChart hπ data H m hj u hu ≫ p =
      chartStructure Q t :=
  PolygonVariableSmoothing.chartWithParameter_toBase Q 5
    (arithmeticZeroDiagonalPolygonParameter hπ data H hj u hu m) (by omega) _ _ _

/-- The whole retained comparison uses the actual original global source base. -/
@[reassoc] theorem arithmeticZeroDiagonalPolygonRetainedMap_original_base (b : Bool) :
    arithmeticZeroDiagonalPolygonRetainedMap hπ data H m hj u hu b ≫ p =
      ι (.retained ⟨0, by omega⟩ b) ≫ q := by
  rw [arithmeticZeroDiagonalPolygonRetainedMap_base, arithmeticZeroDiagonalAtlas_retained_base]

/-- The whole common terminal comparison uses the actual original global source base. -/
@[reassoc] theorem arithmeticZeroDiagonalPolygonTerminalChart_original_base :
    arithmeticZeroDiagonalPolygonTerminalChart hπ data H m hj u hu ≫ p =
      ι .terminal ≫ q := by
  rw [arithmeticZeroDiagonalPolygonTerminalChart_base, arithmeticZeroDiagonalAtlas_terminal_base]

/-- Every point of each full closing union maps over its original arithmetic coefficient base. -/
@[reassoc] theorem arithmeticZeroDiagonalClosingUnionMap_base (b : Bool) :
    F b ≫ p = (U b).ι ≫ q := by
  apply (cancel_epi (J b).hom).mp
  apply pushout.hom_ext
  · have h := arithmeticZeroDiagonalClosingUnionMap_retained hπ data H m hj u hu b
    have h' := congrArg (· ≫ p) h
    simp only [Category.assoc] at h' ⊢
    rw [h', arithmeticZeroDiagonalPolygonRetainedMap_original_base,
      arithmeticZeroDiagonalClosingUnionIso_global_assoc,
      arithmeticZeroDiagonalClosingToGlobal_retained_assoc]
  · have h := arithmeticZeroDiagonalClosingUnionMap_terminal hπ data H m hj u hu b
    have h' := congrArg (· ≫ p) h
    simp only [Category.assoc] at h' ⊢
    rw [h', arithmeticZeroDiagonalPolygonTerminalChart_original_base,
      arithmeticZeroDiagonalClosingUnionIso_global_assoc,
      arithmeticZeroDiagonalClosingToGlobal_terminal_assoc]

/-- Both complete source closing unions carry a comparison in the category over the base. -/
def arithmeticZeroDiagonalClosingUnionComparisonOver (b : Bool) :
    Over.mk ((U b).ι ≫ q) ⟶ Over.mk p :=
  Over.homMk (F b) (arithmeticZeroDiagonalClosingUnionMap_base hπ data H m hj u hu b)

end FLT.Mazur.WeierstrassDividedDepth
