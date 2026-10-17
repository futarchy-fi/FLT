/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthFartherAtlas

/-!
# The fifth depth-three corrected atlas over all arithmetic quotients

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
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u) (ha : 3 = j)
local notation "A" => fun m ↦ arithmeticFifthFartherAtlasObject hπ data H m j hj u hu
local notation "E" => fun m ↦ arithmeticFifthFartherAtlasCorrection hπ data H m j hj u hu ha
local notation "ι" => fun m ↦ arithmeticFifthFartherAtlasChart hπ data H m j hj u hu ha
local notation "ρ" => arithmeticFourthOuterAtlasRestriction hπ data H j hj u hu
local notation "q" => simultaneousTwistedArithmeticRestriction hπ data H

/-- The original arithmetic quotient transported through the full fifth corrections. -/
def arithmeticFifthFartherAtlasRestriction (m : ℕ) (i : ArithmeticChartLabel (j + 1)) :
    A m i ⟶ A (m + 1) i :=
  (E m i).inv ≫ ρ m i ≫ (E (m + 1) i).hom

local notation "S" => arithmeticFifthFartherAtlasRestriction hπ data H j hj u hu ha

omit [IsBezout R] in
/-- Each correction is an exact square for the original arithmetic quotient. -/
@[reassoc] theorem arithmeticFifthFartherAtlasCorrection_restriction
    (m : ℕ) (i : ArithmeticChartLabel (j + 1)) :
    (E m i).hom ≫ S m i = ρ m i ≫ (E (m + 1) i).hom := by
  rw [arithmeticFifthFartherAtlasRestriction, Iso.hom_inv_id_assoc]

/-- Every full lifted chart inclusion respects the actual global quotient arrow. -/
@[reassoc] theorem arithmeticFifthFartherAtlasChart_restriction
    (m : ℕ) (i : ArithmeticChartLabel (j + 1)) :
    S m i ≫ ι (m + 1) i = ι m i ≫ q m j hj u hu := by
  dsimp only
  rw [arithmeticFifthFartherAtlasRestriction, arithmeticFifthFartherAtlasChart,
    arithmeticFifthFartherAtlasChart, Category.assoc, Category.assoc,
    Iso.hom_inv_id_assoc, arithmeticFourthOuterAtlasChart_restriction, Category.assoc]

/-- One full corrected labeled chart at every arithmetic quotient order. -/
def arithmeticFifthFartherChartSystem (i : ArithmeticChartLabel (j + 1)) : ℕ ⥤ Scheme :=
  Functor.ofSequence (fun m ↦ S m i)

/-- The complete lifted cover maps naturally into the original complete arithmetic target. -/
def arithmeticFifthFartherChartSystemMap (i : ArithmeticChartLabel (j + 1)) :
    arithmeticFifthFartherChartSystem hπ data H j hj u hu ha i ⟶
      changedArithmeticTargetSystem hπ data H j hj u hu :=
  NatTrans.ofSequence (fun m ↦ ι m i) (by
    intro m
    simpa only [arithmeticFifthFartherChartSystem, changedArithmeticTargetSystem,
      Functor.ofSequence_obj, Functor.ofSequence_map_homOfLE_succ] using
        arithmeticFifthFartherAtlasChart_restriction hπ data H j hj u hu ha m i)

/-- The complete chart comparison is compatible with every nonconsecutive quotient too. -/
@[reassoc] theorem arithmeticFifthFartherChartSystemMap_naturality
    (i : ArithmeticChartLabel (j + 1)) {a b : ℕ} (hab : a ≤ b) :
    (arithmeticFifthFartherChartSystem hπ data H j hj u hu ha i).map (homOfLE hab) ≫ ι b i =
      ι a i ≫ (changedArithmeticTargetSystem hπ data H j hj u hu).map (homOfLE hab) :=
  (arithmeticFifthFartherChartSystemMap hπ data H j hj u hu ha i).naturality (homOfLE hab)

end FLT.Mazur.WeierstrassDividedDepth
