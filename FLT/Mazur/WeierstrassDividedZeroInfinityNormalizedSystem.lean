/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedFullRestriction

/-!
# The complete original three-chart union and normalized pair as quotient systems

The constructed comparison is a natural isomorphism over the full original
coefficient system. Naturality includes nonconsecutive arithmetic orders.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFiniteInitialIso arithmeticInitialFactorRatioChart arithmeticZeroFiniteAtlasIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "U" => fun k ↦ arithmeticZeroInfinityNormalizedFullUnion hπ data H k hj u hu
local notation "F" => fun k ↦ arithmeticZeroInfinityNormalizedFullComparison hπ data H k hj u hu
local notation "B" => fun k ↦ arithmeticZeroDiagonalSourceToBase hπ data H k hj u hu
local notation "p" => fun k ↦ arithmeticZeroInfinityNormalizedTargetToBase data H k

/-- The full original three-chart unions with their actual global quotient restrictions. -/
def arithmeticZeroInfinityNormalizedFullUnionSystem : ℕ ⥤ Scheme :=
  Functor.ofSequence (fun k ↦ arithmeticZeroInfinityNormalizedFullUnionRestriction
    hπ data H k hj u hu)

/-- The independent normalized pairs with the original whole-node coefficient arrows. -/
def arithmeticZeroInfinityNormalizedTargetSystem : ℕ ⥤ Scheme :=
  Functor.ofSequence (fun k ↦ arithmeticZeroInfinityNormalizedTargetRestriction data H k)

local notation "X" => arithmeticZeroInfinityNormalizedFullUnionSystem hπ data H hj u hu
local notation "Y" => arithmeticZeroInfinityNormalizedTargetSystem data H

/-- The whole original comparison preserves every arithmetic quotient arrow. -/
def arithmeticZeroInfinityNormalizedFullComparisonSystem : X ⟶ Y :=
  NatTrans.ofSequence (fun k ↦ (F k).hom) (by
    intro k
    simpa only [arithmeticZeroInfinityNormalizedFullUnionSystem,
      arithmeticZeroInfinityNormalizedTargetSystem, Functor.ofSequence_obj,
      Functor.ofSequence_map_homOfLE_succ] using
      arithmeticZeroInfinityNormalizedFullComparison_restriction hπ data H k hj u hu)

/-- The complete source-union comparison is a natural isomorphism at all quotient orders. -/
def arithmeticZeroInfinityNormalizedFullComparisonSystemIso : X ≅ Y :=
  NatIso.ofComponents F (fun {_ _} f ↦
    (arithmeticZeroInfinityNormalizedFullComparisonSystem hπ data H hj u hu).naturality f)

/-- The actual original union system has its full global coefficient projection. -/
def arithmeticZeroInfinityNormalizedFullUnionSystemStructure : X ⟶ baseSystem R π :=
  NatTrans.ofSequence (fun k ↦ (U k).ι ≫ B k) (by
    intro k
    simpa only [arithmeticZeroInfinityNormalizedFullUnionSystem, baseSystem,
      Functor.ofSequence_obj, Functor.ofSequence_map_homOfLE_succ, Category.assoc] using
      arithmeticZeroInfinityNormalizedFullUnionRestriction_base hπ data H k hj u hu)

/-- The independent target system keeps its original quotient coefficients. -/
def arithmeticZeroInfinityNormalizedTargetSystemStructure : Y ⟶ baseSystem R π :=
  NatTrans.ofSequence p (by
    intro k
    simpa only [arithmeticZeroInfinityNormalizedTargetSystem, baseSystem,
      Functor.ofSequence_obj, Functor.ofSequence_map_homOfLE_succ] using
      arithmeticZeroInfinityNormalizedTargetRestriction_base hπ data H k hj u hu)

/-- The complete natural comparison lies over the original arithmetic coefficient system. -/
theorem arithmeticZeroInfinityNormalizedFullComparisonSystem_base :
    arithmeticZeroInfinityNormalizedFullComparisonSystem hπ data H hj u hu ≫
      arithmeticZeroInfinityNormalizedTargetSystemStructure hπ data H hj u hu =
        arithmeticZeroInfinityNormalizedFullUnionSystemStructure hπ data H hj u hu := by
  ext k : 2
  exact arithmeticZeroInfinityNormalizedFullComparison_base hπ data H k hj u hu

/-- The actual original comparison commutes with every nonconsecutive quotient square. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedFullComparisonSystem_naturality
    {i j : ℕ} (hij : i ≤ j) :
    (X).map (homOfLE hij) ≫ (F j).hom = (F i).hom ≫ (Y).map (homOfLE hij) :=
  (arithmeticZeroInfinityNormalizedFullComparisonSystem hπ data H hj u hu).naturality _

/-- Every nonconsecutive source quotient retains the original coefficient base. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedFullUnionSystemStructure_naturality
    {i j : ℕ} (hij : i ≤ j) :
    (X).map (homOfLE hij) ≫ (U j).ι ≫ B j =
      (U i).ι ≫ B i ≫ (baseSystem R π).map (homOfLE hij) := by
  exact ((arithmeticZeroInfinityNormalizedFullUnionSystemStructure hπ data H hj u hu).naturality
    (homOfLE hij)).trans (Category.assoc _ _ _)

end FLT.Mazur.WeierstrassDividedDepth
