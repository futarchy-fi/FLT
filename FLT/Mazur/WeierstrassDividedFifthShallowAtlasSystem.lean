/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthShallowAtlas

/-!
# The fifth depth-two corrected atlas over all arithmetic quotients

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
  (H : ArithmeticAtlasCoefficients data) (hj : 3 ≤ n)
  (u : Rˣ) (hu : (data ⟨3, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "A" => fun m ↦ arithmeticFifthShallowAtlasObject hπ data H m hj u hu
local notation "E" => fun m ↦ arithmeticFifthShallowAtlasCorrection hπ data H m hj u hu
local notation "ι" => fun m ↦ arithmeticFifthShallowAtlasChart hπ data H m hj u hu
local notation "ρ" => arithmeticFourthShallowAtlasRestriction hπ data H 2 hj u hu
local notation "q" => simultaneousTwistedArithmeticRestriction hπ data H

/-- The original arithmetic quotient transported through the full fifth corrections. -/
def arithmeticFifthShallowAtlasRestriction (m : ℕ) (i : ArithmeticChartLabel 3) :
    A m i ⟶ A (m + 1) i :=
  (E m i).inv ≫ ρ m i ≫ (E (m + 1) i).hom

local notation "S" => arithmeticFifthShallowAtlasRestriction hπ data H hj u hu

omit [IsBezout R] in
/-- Each correction is an exact square for the original arithmetic quotient. -/
@[reassoc] theorem arithmeticFifthShallowAtlasCorrection_restriction
    (m : ℕ) (i : ArithmeticChartLabel 3) :
    (E m i).hom ≫ S m i = ρ m i ≫ (E (m + 1) i).hom := by
  rw [arithmeticFifthShallowAtlasRestriction, Iso.hom_inv_id_assoc]

/-- Every full lifted chart inclusion respects the actual global quotient arrow. -/
@[reassoc] theorem arithmeticFifthShallowAtlasChart_restriction
    (m : ℕ) (i : ArithmeticChartLabel 3) :
    S m i ≫ ι (m + 1) i = ι m i ≫ q m 2 hj u hu := by
  dsimp only
  rw [arithmeticFifthShallowAtlasRestriction, arithmeticFifthShallowAtlasChart,
    arithmeticFifthShallowAtlasChart, Category.assoc, Category.assoc,
    Iso.hom_inv_id_assoc, arithmeticFourthShallowAtlasChart_restriction, Category.assoc]

/-- One full corrected labeled chart at every arithmetic quotient order. -/
def arithmeticFifthShallowChartSystem (i : ArithmeticChartLabel 3) : ℕ ⥤ Scheme :=
  Functor.ofSequence (fun m ↦ S m i)

/-- The complete lifted cover maps naturally into the original complete arithmetic target. -/
def arithmeticFifthShallowChartSystemMap (i : ArithmeticChartLabel 3) :
    arithmeticFifthShallowChartSystem hπ data H hj u hu i ⟶
      changedArithmeticTargetSystem hπ data H 2 hj u hu :=
  NatTrans.ofSequence (fun m ↦ ι m i) (by
    intro m
    simpa only [arithmeticFifthShallowChartSystem, changedArithmeticTargetSystem,
      Functor.ofSequence_obj, Functor.ofSequence_map_homOfLE_succ] using
        arithmeticFifthShallowAtlasChart_restriction hπ data H hj u hu m i)

/-- The complete chart comparison is compatible with every nonconsecutive quotient too. -/
@[reassoc] theorem arithmeticFifthShallowChartSystemMap_naturality
    (i : ArithmeticChartLabel 3) {a b : ℕ} (hab : a ≤ b) :
    (arithmeticFifthShallowChartSystem hπ data H hj u hu i).map (homOfLE hab) ≫ ι b i =
      ι a i ≫ (changedArithmeticTargetSystem hπ data H 2 hj u hu).map (homOfLE hab) :=
  (arithmeticFifthShallowChartSystemMap hπ data H hj u hu i).naturality (homOfLE hab)

end FLT.Mazur.WeierstrassDividedDepth
