/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOneDiagonalAtlas
public import FLT.Mazur.WeierstrassDividedFifthInitialAtlasSystem

/-!
# The diagonal depth-one corrected atlas over all arithmetic quotients

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
  (H : ArithmeticAtlasCoefficients data) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "A" => fun m ↦ arithmeticOneDiagonalAtlasObject hπ data H m hj u hu
local notation "E" => fun m ↦ arithmeticOneDiagonalAtlasCorrection hπ data H m hj u hu
local notation "ι" => fun m ↦ arithmeticOneDiagonalAtlasChart hπ data H m hj u hu
local notation "ρ" => arithmeticFifthInitialAtlasRestriction hπ data H hj u hu
local notation "q" => simultaneousTwistedArithmeticRestriction hπ data H

/-- The original arithmetic quotient transported through the full finite corrections. -/
def arithmeticOneDiagonalAtlasRestriction (m : ℕ) (i : ArithmeticChartLabel 2) :
    A m i ⟶ A (m + 1) i :=
  (E m i).inv ≫ ρ m i ≫ (E (m + 1) i).hom

local notation "S" => arithmeticOneDiagonalAtlasRestriction hπ data H hj u hu

omit [IsBezout R] in
/-- Each correction is an exact square for the original arithmetic quotient. -/
@[reassoc] theorem arithmeticOneDiagonalAtlasCorrection_restriction
    (m : ℕ) (i : ArithmeticChartLabel 2) :
    (E m i).hom ≫ S m i = ρ m i ≫ (E (m + 1) i).hom := by
  rw [arithmeticOneDiagonalAtlasRestriction, Iso.hom_inv_id_assoc]

/-- Every full lifted chart inclusion respects the actual global quotient arrow. -/
@[reassoc] theorem arithmeticOneDiagonalAtlasChart_restriction
    (m : ℕ) (i : ArithmeticChartLabel 2) :
    S m i ≫ ι (m + 1) i = ι m i ≫ q m 1 hj u hu := by
  apply (cancel_epi (E m i).hom).mp
  rw [← Category.assoc, arithmeticOneDiagonalAtlasCorrection_restriction,
    Category.assoc, arithmeticOneDiagonalAtlasCorrection_chart,
    arithmeticOneDiagonalAtlasCorrection_chart_assoc,
    arithmeticFifthInitialAtlasChart_restriction]

/-- One full corrected labeled chart at every arithmetic quotient order. -/
def arithmeticOneDiagonalChartSystem (i : ArithmeticChartLabel 2) : ℕ ⥤ Scheme :=
  Functor.ofSequence (fun m ↦ S m i)

/-- The complete lifted cover maps naturally into the original complete arithmetic target. -/
def arithmeticOneDiagonalChartSystemMap (i : ArithmeticChartLabel 2) :
    arithmeticOneDiagonalChartSystem hπ data H hj u hu i ⟶
      changedArithmeticTargetSystem hπ data H 1 hj u hu :=
  NatTrans.ofSequence (fun m ↦ ι m i) (by
    intro m
    simpa only [arithmeticOneDiagonalChartSystem, changedArithmeticTargetSystem,
      Functor.ofSequence_obj, Functor.ofSequence_map_homOfLE_succ] using
        arithmeticOneDiagonalAtlasChart_restriction hπ data H hj u hu m i)

/-- The complete chart comparison is compatible with every nonconsecutive quotient too. -/
@[reassoc] theorem arithmeticOneDiagonalChartSystemMap_naturality
    (i : ArithmeticChartLabel 2) {a b : ℕ} (hab : a ≤ b) :
    (arithmeticOneDiagonalChartSystem hπ data H hj u hu i).map (homOfLE hab) ≫ ι b i =
      ι a i ≫ (changedArithmeticTargetSystem hπ data H 1 hj u hu).map (homOfLE hab) :=
  (arithmeticOneDiagonalChartSystemMap hπ data H hj u hu i).naturality (homOfLE hab)

end FLT.Mazur.WeierstrassDividedDepth
