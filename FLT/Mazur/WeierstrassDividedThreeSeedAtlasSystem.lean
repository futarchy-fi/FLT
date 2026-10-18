/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThreeSeedAtlas
public import FLT.Mazur.WeierstrassDividedFifthFartherAtlasSystem

/-!
# The uniform depth-three seed atlas over all arithmetic quotients

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
  (H : ArithmeticAtlasCoefficients data) (hj : 4 ≤ n)
  (u : Rˣ) (hu : (data ⟨4, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "A" => fun m ↦ arithmeticThreeSeedAtlasObject hπ data H m hj u hu
local notation "E" => fun m ↦ arithmeticThreeSeedIdentification hπ data H m hj u hu
local notation "ι" => fun m ↦ arithmeticThreeSeedAtlasChart hπ data H m hj u hu
local notation "ρ" => arithmeticFifthFartherAtlasRestriction hπ data H 3 hj u hu rfl
local notation "q" => simultaneousTwistedArithmeticRestriction hπ data H

/-- The original arithmetic quotient transported through the seed identifications. -/
def arithmeticThreeSeedAtlasRestriction (m : ℕ) (i : ArithmeticChartLabel 4) :
    A m i ⟶ A (m + 1) i :=
  (E m i).hom ≫ ρ m i ≫ (E (m + 1) i).inv

local notation "S" => arithmeticThreeSeedAtlasRestriction hπ data H hj u hu

omit [IsBezout R] in
/-- Each correction is an exact square for the original arithmetic quotient. -/
@[reassoc] theorem arithmeticThreeSeedIdentification_restriction
    (m : ℕ) (i : ArithmeticChartLabel 4) :
    (E m i).inv ≫ S m i = ρ m i ≫ (E (m + 1) i).inv := by
  rw [arithmeticThreeSeedAtlasRestriction, Iso.inv_hom_id_assoc]

/-- Every full lifted chart inclusion respects the actual global quotient arrow. -/
@[reassoc] theorem arithmeticThreeSeedAtlasChart_restriction
    (m : ℕ) (i : ArithmeticChartLabel 4) :
    S m i ≫ ι (m + 1) i = ι m i ≫ q m 3 hj u hu := by
  dsimp only
  rw [arithmeticThreeSeedAtlasRestriction, arithmeticThreeSeedAtlasChart,
    arithmeticThreeSeedAtlasChart, Category.assoc, Category.assoc,
    Iso.inv_hom_id_assoc, arithmeticFifthFartherAtlasChart_restriction, Category.assoc]

/-- One full corrected labeled chart at every arithmetic quotient order. -/
def arithmeticThreeSeedChartSystem (i : ArithmeticChartLabel 4) : ℕ ⥤ Scheme :=
  Functor.ofSequence (fun m ↦ S m i)

/-- The complete lifted cover maps naturally into the original complete arithmetic target. -/
def arithmeticThreeSeedChartSystemMap (i : ArithmeticChartLabel 4) :
    arithmeticThreeSeedChartSystem hπ data H hj u hu i ⟶
      changedArithmeticTargetSystem hπ data H 3 hj u hu :=
  NatTrans.ofSequence (fun m ↦ ι m i) (by
    intro m
    simpa only [arithmeticThreeSeedChartSystem, changedArithmeticTargetSystem,
      Functor.ofSequence_obj, Functor.ofSequence_map_homOfLE_succ] using
        arithmeticThreeSeedAtlasChart_restriction hπ data H hj u hu m i)

/-- The complete chart comparison is compatible with every nonconsecutive quotient too. -/
@[reassoc] theorem arithmeticThreeSeedChartSystemMap_naturality
    (i : ArithmeticChartLabel 4) {a b : ℕ} (hab : a ≤ b) :
    (arithmeticThreeSeedChartSystem hπ data H hj u hu i).map (homOfLE hab) ≫ ι b i =
      ι a i ≫ (changedArithmeticTargetSystem hπ data H 3 hj u hu).map (homOfLE hab) :=
  (arithmeticThreeSeedChartSystemMap hπ data H hj u hu i).naturality (homOfLE hab)

end FLT.Mazur.WeierstrassDividedDepth
