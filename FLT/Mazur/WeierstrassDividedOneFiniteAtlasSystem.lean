/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOneFiniteAtlas
public import FLT.Mazur.WeierstrassDividedFifthInitialAtlasSystem

/-!
# The finite depth-one corrected atlas over all arithmetic quotients

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
  (H : ArithmeticAtlasCoefficients data) (k : ℕ) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "A" => fun m ↦ arithmeticOneFiniteAtlasObject hπ data H k m hj u hu
local notation "E" => fun m ↦ arithmeticOneFiniteAtlasCorrection hπ data H k m hj u hu
local notation "ι" => fun m ↦ arithmeticOneFiniteAtlasChart hπ data H k m hj u hu
local notation "ρ" => arithmeticFifthInitialAtlasRestriction hπ data H hj u hu
local notation "q" => simultaneousTwistedArithmeticRestriction hπ data H

/-- The original arithmetic quotient transported through the full finite corrections. -/
def arithmeticOneFiniteAtlasRestriction (m : ℕ) (i : ArithmeticChartLabel 2) :
    A m i ⟶ A (m + 1) i :=
  (E m i).inv ≫ ρ m i ≫ (E (m + 1) i).hom

local notation "S" => arithmeticOneFiniteAtlasRestriction hπ data H k hj u hu

omit [IsBezout R] in
/-- Each correction is an exact square for the original arithmetic quotient. -/
@[reassoc] theorem arithmeticOneFiniteAtlasCorrection_restriction
    (m : ℕ) (i : ArithmeticChartLabel 2) :
    (E m i).hom ≫ S m i = ρ m i ≫ (E (m + 1) i).hom := by
  rw [arithmeticOneFiniteAtlasRestriction, Iso.hom_inv_id_assoc]

/-- Every full lifted chart inclusion respects the actual global quotient arrow. -/
@[reassoc] theorem arithmeticOneFiniteAtlasChart_restriction
    (m : ℕ) (i : ArithmeticChartLabel 2) :
    S m i ≫ ι (m + 1) i = ι m i ≫ q m 1 hj u hu := by
  dsimp only
  rw [arithmeticOneFiniteAtlasRestriction, arithmeticOneFiniteAtlasChart,
    arithmeticOneFiniteAtlasChart, Category.assoc, Category.assoc,
    Iso.hom_inv_id_assoc, arithmeticFifthInitialAtlasChart_restriction, Category.assoc]

/-- One full corrected labeled chart at every arithmetic quotient order. -/
def arithmeticOneFiniteChartSystem (i : ArithmeticChartLabel 2) : ℕ ⥤ Scheme :=
  Functor.ofSequence (fun m ↦ S m i)

/-- The complete lifted cover maps naturally into the original complete arithmetic target. -/
def arithmeticOneFiniteChartSystemMap (i : ArithmeticChartLabel 2) :
    arithmeticOneFiniteChartSystem hπ data H k hj u hu i ⟶
      changedArithmeticTargetSystem hπ data H 1 hj u hu :=
  NatTrans.ofSequence (fun m ↦ ι m i) (by
    intro m
    simpa only [arithmeticOneFiniteChartSystem, changedArithmeticTargetSystem,
      Functor.ofSequence_obj, Functor.ofSequence_map_homOfLE_succ] using
        arithmeticOneFiniteAtlasChart_restriction hπ data H k hj u hu m i)

/-- The complete chart comparison is compatible with every nonconsecutive quotient too. -/
@[reassoc] theorem arithmeticOneFiniteChartSystemMap_naturality
    (i : ArithmeticChartLabel 2) {a b : ℕ} (hab : a ≤ b) :
    (arithmeticOneFiniteChartSystem hπ data H k hj u hu i).map (homOfLE hab) ≫ ι b i =
      ι a i ≫ (changedArithmeticTargetSystem hπ data H 1 hj u hu).map (homOfLE hab) :=
  (arithmeticOneFiniteChartSystemMap hπ data H k hj u hu i).naturality (homOfLE hab)

end FLT.Mazur.WeierstrassDividedDepth
