/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOneInfinityNormalizedFullRestriction

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
  arithmeticOneFiniteInitialIso arithmeticInitialFactorRatioChart arithmeticOneFiniteAtlasIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "U" => fun k ↦ arithmeticOneInfinityNormalizedFullUnion hπ data H k hj u hu
local notation "F" => fun k ↦ arithmeticOneInfinityNormalizedFullComparison hπ data H k hj u hu
local notation "B" => fun k ↦ arithmeticOneDiagonalSourceToBase hπ data H k hj u hu
local notation "p" => fun k ↦ arithmeticOneInfinityNormalizedTargetToBase data H k

/-- The full original three-chart unions with their actual global quotient restrictions. -/
def arithmeticOneInfinityNormalizedFullUnionSystem : ℕ ⥤ Scheme :=
  Functor.ofSequence (fun k ↦ arithmeticOneInfinityNormalizedFullUnionRestriction
    hπ data H k hj u hu)

/-- The independent normalized pairs with the original whole-node coefficient arrows. -/
def arithmeticOneInfinityNormalizedTargetSystem : ℕ ⥤ Scheme :=
  Functor.ofSequence (fun k ↦ arithmeticOneInfinityNormalizedTargetRestriction data H k)

local notation "X" => arithmeticOneInfinityNormalizedFullUnionSystem hπ data H hj u hu
local notation "Y" => arithmeticOneInfinityNormalizedTargetSystem data H

/-- The whole original comparison preserves every arithmetic quotient arrow. -/
def arithmeticOneInfinityNormalizedFullComparisonSystem : X ⟶ Y :=
  NatTrans.ofSequence (fun k ↦ (F k).hom) (by
    intro k
    simpa only [arithmeticOneInfinityNormalizedFullUnionSystem,
      arithmeticOneInfinityNormalizedTargetSystem, Functor.ofSequence_obj,
      Functor.ofSequence_map_homOfLE_succ] using
      arithmeticOneInfinityNormalizedFullComparison_restriction hπ data H k hj u hu)

/-- The complete source-union comparison is a natural isomorphism at all quotient orders. -/
def arithmeticOneInfinityNormalizedFullComparisonSystemIso : X ≅ Y :=
  NatIso.ofComponents F (fun {_ _} f ↦
    (arithmeticOneInfinityNormalizedFullComparisonSystem hπ data H hj u hu).naturality f)

/-- The actual original union system has its full global coefficient projection. -/
def arithmeticOneInfinityNormalizedFullUnionSystemStructure : X ⟶ baseSystem R π :=
  NatTrans.ofSequence (fun k ↦ (U k).ι ≫ B k) (by
    intro k
    simpa only [arithmeticOneInfinityNormalizedFullUnionSystem, baseSystem,
      Functor.ofSequence_obj, Functor.ofSequence_map_homOfLE_succ, Category.assoc] using
      arithmeticOneInfinityNormalizedFullUnionRestriction_base hπ data H k hj u hu)

/-- The independent target system keeps its original quotient coefficients. -/
def arithmeticOneInfinityNormalizedTargetSystemStructure : Y ⟶ baseSystem R π :=
  NatTrans.ofSequence p (by
    intro k
    simpa only [arithmeticOneInfinityNormalizedTargetSystem, baseSystem,
      Functor.ofSequence_obj, Functor.ofSequence_map_homOfLE_succ] using
      arithmeticOneInfinityNormalizedTargetRestriction_base hπ data H k hj u hu)

/-- The complete natural comparison lies over the original arithmetic coefficient system. -/
theorem arithmeticOneInfinityNormalizedFullComparisonSystem_base :
    arithmeticOneInfinityNormalizedFullComparisonSystem hπ data H hj u hu ≫
      arithmeticOneInfinityNormalizedTargetSystemStructure hπ data H hj u hu =
        arithmeticOneInfinityNormalizedFullUnionSystemStructure hπ data H hj u hu := by
  ext k : 2
  exact arithmeticOneInfinityNormalizedFullComparison_base hπ data H k hj u hu

/-- The actual original comparison commutes with every nonconsecutive quotient square. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedFullComparisonSystem_naturality
    {i j : ℕ} (hij : i ≤ j) :
    (X).map (homOfLE hij) ≫ (F j).hom = (F i).hom ≫ (Y).map (homOfLE hij) :=
  (arithmeticOneInfinityNormalizedFullComparisonSystem hπ data H hj u hu).naturality _

/-- Every nonconsecutive source quotient retains the original coefficient base. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedFullUnionSystemStructure_naturality
    {i j : ℕ} (hij : i ≤ j) :
    (X).map (homOfLE hij) ≫ (U j).ι ≫ B j =
      (U i).ι ≫ B i ≫ (baseSystem R π).map (homOfLE hij) := by
  exact ((arithmeticOneInfinityNormalizedFullUnionSystemStructure hπ data H hj u hu).naturality
    (homOfLE hij)).trans (Category.assoc _ _ _)

end FLT.Mazur.WeierstrassDividedDepth
