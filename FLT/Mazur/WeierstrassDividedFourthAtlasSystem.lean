/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthAtlas

/-!
# The fourth corrected atlas over all arithmetic quotients

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
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "A" => fun m ↦ arithmeticFourthAtlasObject hπ data H m j hj u hu
local notation "E" => fun m ↦ arithmeticFourthAtlasCorrection hπ data H m j hj u hu
local notation "ι" => fun m ↦ arithmeticFourthAtlasChart hπ data H m j hj u hu
local notation "ρ" => arithmeticThirdInitialAtlasRestriction hπ data H j hj u hu
local notation "q" => simultaneousTwistedArithmeticRestriction hπ data H

/-- The original arithmetic quotient transported through the full fourth corrections. -/
def arithmeticFourthAtlasRestriction (m : ℕ) (i : ArithmeticChartLabel (j + 1)) :
    A m i ⟶ A (m + 1) i :=
  (E m i).inv ≫ ρ m i ≫ (E (m + 1) i).hom

local notation "S" => arithmeticFourthAtlasRestriction hπ data H j hj u hu

omit [IsBezout R] in
/-- Each correction is an exact square for the original arithmetic quotient. -/
@[reassoc] theorem arithmeticFourthAtlasCorrection_restriction
    (m : ℕ) (i : ArithmeticChartLabel (j + 1)) :
    (E m i).hom ≫ S m i = ρ m i ≫ (E (m + 1) i).hom := by
  rw [arithmeticFourthAtlasRestriction, Iso.hom_inv_id_assoc]

/-- Every full lifted chart inclusion respects the actual global quotient arrow. -/
@[reassoc] theorem arithmeticFourthAtlasChart_restriction
    (m : ℕ) (i : ArithmeticChartLabel (j + 1)) :
    S m i ≫ ι (m + 1) i = ι m i ≫ q m j hj u hu := by
  dsimp only
  rw [arithmeticFourthAtlasRestriction, arithmeticFourthAtlasChart,
    arithmeticFourthAtlasChart, Category.assoc, Category.assoc,
    Iso.hom_inv_id_assoc, arithmeticThirdInitialAtlasChart_restriction, Category.assoc]

/-- One full corrected labeled chart at every arithmetic quotient order. -/
def arithmeticFourthChartSystem (i : ArithmeticChartLabel (j + 1)) : ℕ ⥤ Scheme :=
  Functor.ofSequence (fun m ↦ S m i)

/-- The complete lifted cover maps naturally into the original complete arithmetic target. -/
def arithmeticFourthChartSystemMap (i : ArithmeticChartLabel (j + 1)) :
    arithmeticFourthChartSystem hπ data H j hj u hu i ⟶
      changedArithmeticTargetSystem hπ data H j hj u hu :=
  NatTrans.ofSequence (fun m ↦ ι m i) (by
    intro m
    simpa only [arithmeticFourthChartSystem, changedArithmeticTargetSystem,
      Functor.ofSequence_obj, Functor.ofSequence_map_homOfLE_succ] using
        arithmeticFourthAtlasChart_restriction hπ data H j hj u hu m i)

/-- The complete chart comparison is compatible with every nonconsecutive quotient too. -/
@[reassoc] theorem arithmeticFourthChartSystemMap_naturality
    (i : ArithmeticChartLabel (j + 1)) {a b : ℕ} (hab : a ≤ b) :
    (arithmeticFourthChartSystem hπ data H j hj u hu i).map (homOfLE hab) ≫ ι b i =
      ι a i ≫ (changedArithmeticTargetSystem hπ data H j hj u hu).map (homOfLE hab) :=
  (arithmeticFourthChartSystemMap hπ data H j hj u hu i).naturality (homOfLE hab)

end FLT.Mazur.WeierstrassDividedDepth
