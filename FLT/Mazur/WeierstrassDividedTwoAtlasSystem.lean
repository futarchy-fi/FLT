/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthShallowAtlasSystem
public import FLT.Mazur.WeierstrassDividedTwoDiagonalAtlas
public import FLT.Mazur.WeierstrassDividedTwoFiniteAtlas

/-!
# The finite depth-two corrected atlas over all arithmetic quotients

The exact original quotient maps are transported through the installed chart
corrections. Every labeled chart remains natural in the complete target.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (k : ℕ) (hj : 3 ≤ n)
  (u : Rˣ) (hu : (data ⟨3, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "A" => fun m ↦ arithmeticTwoFiniteAtlasObject hπ data H k m hj u hu
local notation "E" => fun m ↦ arithmeticTwoFiniteAtlasCorrection hπ data H k m hj u hu
local notation "ι" => fun m ↦ arithmeticTwoFiniteAtlasChart hπ data H k m hj u hu
local notation "ρ" => arithmeticFifthShallowAtlasRestriction hπ data H hj u hu
local notation "q" => simultaneousTwistedArithmeticRestriction hπ data H

/-- The original arithmetic quotient transported through the full finite corrections. -/
def arithmeticTwoFiniteAtlasRestriction (m : ℕ) (i : ArithmeticChartLabel 3) :
    A m i ⟶ A (m + 1) i :=
  (E m i).inv ≫ ρ m i ≫ (E (m + 1) i).hom

local notation "S" => arithmeticTwoFiniteAtlasRestriction hπ data H k hj u hu

omit [IsBezout R] in
/-- Each correction is an exact square for the original arithmetic quotient. -/
@[reassoc] theorem arithmeticTwoFiniteAtlasCorrection_restriction
    (m : ℕ) (i : ArithmeticChartLabel 3) :
    (E m i).hom ≫ S m i = ρ m i ≫ (E (m + 1) i).hom := by
  rw [arithmeticTwoFiniteAtlasRestriction, Iso.hom_inv_id_assoc]

/-- Every full lifted chart inclusion respects the actual global quotient arrow. -/
@[reassoc] theorem arithmeticTwoFiniteAtlasChart_restriction
    (m : ℕ) (i : ArithmeticChartLabel 3) :
    S m i ≫ ι (m + 1) i = ι m i ≫ q m 2 hj u hu := by
  dsimp only
  rw [arithmeticTwoFiniteAtlasRestriction, arithmeticTwoFiniteAtlasChart,
    arithmeticTwoFiniteAtlasChart, Category.assoc, Category.assoc,
    Iso.hom_inv_id_assoc, arithmeticFifthShallowAtlasChart_restriction, Category.assoc]

/-- One full corrected labeled chart at every arithmetic quotient order. -/
def arithmeticTwoFiniteChartSystem (i : ArithmeticChartLabel 3) : ℕ ⥤ Scheme :=
  Functor.ofSequence (fun m ↦ S m i)

/-- The complete lifted cover maps naturally into the original complete arithmetic target. -/
def arithmeticTwoFiniteChartSystemMap (i : ArithmeticChartLabel 3) :
    arithmeticTwoFiniteChartSystem hπ data H k hj u hu i ⟶
      changedArithmeticTargetSystem hπ data H 2 hj u hu :=
  NatTrans.ofSequence (fun m ↦ ι m i) (by
    intro m
    simpa only [arithmeticTwoFiniteChartSystem, changedArithmeticTargetSystem,
      Functor.ofSequence_obj, Functor.ofSequence_map_homOfLE_succ] using
        arithmeticTwoFiniteAtlasChart_restriction hπ data H k hj u hu m i)

/-- The complete chart comparison is compatible with every nonconsecutive quotient too. -/
@[reassoc] theorem arithmeticTwoFiniteChartSystemMap_naturality
    (i : ArithmeticChartLabel 3) {a b : ℕ} (hab : a ≤ b) :
    (arithmeticTwoFiniteChartSystem hπ data H k hj u hu i).map (homOfLE hab) ≫ ι b i =
      ι a i ≫ (changedArithmeticTargetSystem hπ data H 2 hj u hu).map (homOfLE hab) :=
  (arithmeticTwoFiniteChartSystemMap hπ data H k hj u hu i).naturality (homOfLE hab)

end FLT.Mazur.WeierstrassDividedDepth

/-!
# The diagonal depth-two corrected atlas over all arithmetic quotients

The correction count varies with arithmetic order. Transport of the original
quotient maps through the installed factors makes every inclusion natural.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (hj : 3 ≤ n)
  (u : Rˣ) (hu : (data ⟨3, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "A" => fun m ↦ arithmeticTwoDiagonalAtlasObject hπ data H m hj u hu
local notation "E" => fun m ↦ arithmeticTwoDiagonalAtlasCorrection hπ data H m hj u hu
local notation "ι" => fun m ↦ arithmeticTwoDiagonalAtlasChart hπ data H m hj u hu
local notation "ρ" => arithmeticFifthShallowAtlasRestriction hπ data H hj u hu
local notation "q" => simultaneousTwistedArithmeticRestriction hπ data H

/-- The original arithmetic quotient transported through the full finite corrections. -/
def arithmeticTwoDiagonalAtlasRestriction (m : ℕ) (i : ArithmeticChartLabel 3) :
    A m i ⟶ A (m + 1) i :=
  (E m i).inv ≫ ρ m i ≫ (E (m + 1) i).hom

local notation "S" => arithmeticTwoDiagonalAtlasRestriction hπ data H hj u hu

omit [IsBezout R] in
/-- Each correction is an exact square for the original arithmetic quotient. -/
@[reassoc] theorem arithmeticTwoDiagonalAtlasCorrection_restriction
    (m : ℕ) (i : ArithmeticChartLabel 3) :
    (E m i).hom ≫ S m i = ρ m i ≫ (E (m + 1) i).hom := by
  rw [arithmeticTwoDiagonalAtlasRestriction, Iso.hom_inv_id_assoc]

/-- Every full lifted chart inclusion respects the actual global quotient arrow. -/
@[reassoc] theorem arithmeticTwoDiagonalAtlasChart_restriction
    (m : ℕ) (i : ArithmeticChartLabel 3) :
    S m i ≫ ι (m + 1) i = ι m i ≫ q m 2 hj u hu := by
  apply (cancel_epi (E m i).hom).mp
  rw [← Category.assoc, arithmeticTwoDiagonalAtlasCorrection_restriction,
    Category.assoc, arithmeticTwoDiagonalAtlasCorrection_chart,
    arithmeticTwoDiagonalAtlasCorrection_chart_assoc,
    arithmeticFifthShallowAtlasChart_restriction]

/-- One full corrected labeled chart at every arithmetic quotient order. -/
def arithmeticTwoDiagonalChartSystem (i : ArithmeticChartLabel 3) : ℕ ⥤ Scheme :=
  Functor.ofSequence (fun m ↦ S m i)

/-- The complete lifted cover maps naturally into the original complete arithmetic target. -/
def arithmeticTwoDiagonalChartSystemMap (i : ArithmeticChartLabel 3) :
    arithmeticTwoDiagonalChartSystem hπ data H hj u hu i ⟶
      changedArithmeticTargetSystem hπ data H 2 hj u hu :=
  NatTrans.ofSequence (fun m ↦ ι m i) (by
    intro m
    simpa only [arithmeticTwoDiagonalChartSystem, changedArithmeticTargetSystem,
      Functor.ofSequence_obj, Functor.ofSequence_map_homOfLE_succ] using
        arithmeticTwoDiagonalAtlasChart_restriction hπ data H hj u hu m i)

/-- The complete chart comparison is compatible with every nonconsecutive quotient too. -/
@[reassoc] theorem arithmeticTwoDiagonalChartSystemMap_naturality
    (i : ArithmeticChartLabel 3) {a b : ℕ} (hab : a ≤ b) :
    (arithmeticTwoDiagonalChartSystem hπ data H hj u hu i).map (homOfLE hab) ≫ ι b i =
      ι a i ≫ (changedArithmeticTargetSystem hπ data H 2 hj u hu).map (homOfLE hab) :=
  (arithmeticTwoDiagonalChartSystemMap hπ data H hj u hu i).naturality (homOfLE hab)

end FLT.Mazur.WeierstrassDividedDepth
