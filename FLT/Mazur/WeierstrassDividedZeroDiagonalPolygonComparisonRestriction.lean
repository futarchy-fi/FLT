/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroDiagonalFactorRatioRestriction
public import FLT.Mazur.WeierstrassDividedZeroDiagonalPolygonExterior
public import FLT.Mazur.WeierstrassDividedRetainedPolygonNaturality

/-!
# Quotient naturality of the actual diagonal polygon comparisons

The identified initial, retained and terminal nodes keep their own coefficient
maps. Both orientations and the full original initial-open maps commute with
the independently constructed target restriction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] arithmeticZeroDiagonalState
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "p" => fun k ↦ arithmeticZeroDiagonalPolygonParameter hπ data H hj u hu k
local notation "D" => arithmeticZeroDiagonalState hπ data H 0 hj u hu
local notation "s" => PolygonArithmeticSimultaneous.State.initial D
local notation "t" => PolygonArithmeticSimultaneous.State.last D
local notation "c" => fun k ↦ arithmeticZeroDiagonalPolygonInitialChart hπ data H k hj u hu
local notation "d" => fun k ↦ arithmeticZeroDiagonalPolygonRetainedChart hπ data H k hj u hu
local notation "C" => fun k ↦ arithmeticZeroDiagonalPolygonInitialMap hπ data H k hj u hu
local notation "F" => fun k ↦ arithmeticZeroDiagonalPolygonRetainedMap hπ data H k hj u hu
local notation "ρ" => arithmeticZeroDiagonalPolygonRestriction hπ data H m hj u hu
local notation "S" => arithmeticZeroDiagonalInitialNodeRestriction hπ data H 0 hj u hu m
local notation "T" => arithmeticZeroDiagonalLastRestriction hπ data H 0 hj u hu m

/-- Each identified initial target node retains its actual diagonal coefficient map. -/
@[reassoc] theorem arithmeticZeroDiagonalPolygonInitialChart_restriction (b : Bool) :
    c m b ≫ ρ = S b ≫ c (m + 1) b :=
  PolygonVariableSmoothing.chartWithParameter_projection _ 5 (p (m + 1)) (by omega)
    (restriction R π m).toRingHom (p m) _ _ _ _ _ _ _

/-- Each identified retained target node retains its actual diagonal coefficient map. -/
@[reassoc] theorem arithmeticZeroDiagonalPolygonRetainedChart_restriction (b : Bool) :
    d m b ≫ ρ = T b ≫ d (m + 1) b :=
  PolygonVariableSmoothing.chartWithParameter_projection _ 5 (p (m + 1)) (by omega)
    (restriction R π m).toRingHom (p m) _ _ _ _ _ _ _

/-- The common terminal target uses the quotient map of its own accumulated smoothing. -/
@[reassoc] theorem arithmeticZeroDiagonalPolygonTerminalChart_restriction :
    arithmeticZeroDiagonalPolygonTerminalChart hπ data H m hj u hu ≫ ρ =
      arithmeticZeroDiagonalTerminalRestriction hπ data H 0 hj u hu m ≫
        arithmeticZeroDiagonalPolygonTerminalChart hπ data H (m + 1) hj u hu :=
  PolygonVariableSmoothing.chartWithParameter_projection _ 5 (p (m + 1)) (by omega)
    (restriction R π m).toRingHom (p m) _ _ _ _ _ _ _

/-- Both oriented initial target maps follow the whole actual coefficient restriction. -/
@[reassoc] theorem arithmeticZeroDiagonalPolygonInitialMap_restriction (b : Bool) :
    C m b ≫ ρ = S b ≫ C (m + 1) b := by
  cases b
  · simp only [arithmeticZeroDiagonalPolygonInitialMap, Bool.false_eq_true, ↓reduceIte,
      Category.id_comp, arithmeticZeroDiagonalPolygonInitialChart_restriction]
  · simp only [arithmeticZeroDiagonalPolygonInitialMap, ↓reduceIte, Category.assoc,
      arithmeticZeroDiagonalPolygonInitialChart_restriction]
    exact branchSwapIso_ringMap_assoc (restriction R π m).toRingHom _ _
      ((arithmeticZeroDiagonalState_compatible hπ data H 0 hj u hu).1 m true) _

/-- Both complete retained comparisons have their exact quotient square. -/
@[reassoc] theorem arithmeticZeroDiagonalPolygonRetainedMap_restriction (b : Bool) :
    F m b ≫ ρ = T b ≫ F (m + 1) b := by
  cases b
  · simp only [arithmeticZeroDiagonalPolygonRetainedMap, Bool.false_eq_true, ↓reduceIte,
      Category.id_comp, arithmeticZeroDiagonalPolygonRetainedChart_restriction]
  · simp only [arithmeticZeroDiagonalPolygonRetainedMap, ↓reduceIte, Category.assoc,
      arithmeticZeroDiagonalPolygonRetainedChart_restriction]
    exact branchSwapIso_ringMap_assoc (restriction R π m).toRingHom _ _
      ((arithmeticZeroDiagonalState_compatible hπ data H 0 hj u hu).2.1 m true) _

/-- Both initial orientations preserve the actual arithmetic coefficient projection. -/
@[reassoc] theorem arithmeticZeroDiagonalPolygonInitialMap_base (b : Bool) :
    C m b ≫ arithmeticZeroDiagonalPolygonToBase hπ data H m hj u hu =
      chartStructure Q (s m b) := by
  cases b <;> simp only [arithmeticZeroDiagonalPolygonInitialMap, Bool.false_eq_true,
    ↓reduceIte, Category.id_comp, Category.assoc,
    arithmeticZeroDiagonalPolygonInitialChart_base, retainedPolygonSwap_base]

/-- Both retained orientations preserve the actual arithmetic coefficient projection. -/
@[reassoc] theorem arithmeticZeroDiagonalPolygonRetainedMap_base (b : Bool) :
    F m b ≫ arithmeticZeroDiagonalPolygonToBase hπ data H m hj u hu =
      chartStructure Q (t m b) := by
  cases b <;> simp only [arithmeticZeroDiagonalPolygonRetainedMap, Bool.false_eq_true,
    ↓reduceIte, Category.id_comp, Category.assoc,
    arithmeticZeroDiagonalPolygonRetainedChart_base, retainedPolygonSwap_base]

variable [IsBezout R]

/-- The entire corrected source initial open maps naturally to the independent target polygon. -/
@[reassoc] theorem arithmeticZeroDiagonalFactorRatioInitialMap_restriction (b : Bool) :
    arithmeticZeroDiagonalInitialRestriction hπ data H 0 hj u hu m b ≫
      arithmeticZeroDiagonalFactorRatioInitialMap hπ data H (m + 1) hj u hu b =
        arithmeticZeroDiagonalFactorRatioInitialMap hπ data H m hj u hu b ≫ ρ := by
  simp only [arithmeticZeroDiagonalFactorRatioInitialMap, Category.assoc,
    arithmeticZeroDiagonalPolygonInitialMap_restriction]
  rw [← Category.assoc, arithmeticZeroDiagonalInitialFactorRatio_restriction, Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth
