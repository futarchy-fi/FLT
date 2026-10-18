/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedRetainedUnionRestriction

/-!
# The full exact retained attachment as an arithmetic quotient system

For either label, the whole actual source union and independent attached target
are naturally isomorphic over the original base system at all orders.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFiniteAtlasIso simultaneousTwistedArithmeticIso
  arithmeticZeroFiniteInitialIso arithmeticInitialFactorRatioChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u) (b : Bool)
local notation "V" => fun k ↦ arithmeticZeroInfinityNormalizedRetainedUnion hπ data H k hj u hu b
local notation "F" => fun k ↦
  arithmeticZeroInfinityNormalizedRetainedComparison hπ data H k hj u hu b
local notation "B" => fun k ↦ arithmeticZeroDiagonalSourceToBase hπ data H k hj u hu
local notation "p" => fun k ↦
  arithmeticZeroInfinityNormalizedRetainedTargetToBase hπ data H k hj u hu b

/-- The whole actual four-chart unions with their original global quotient restrictions. -/
def arithmeticZeroInfinityNormalizedRetainedUnionSystem : ℕ ⥤ Scheme :=
  Functor.ofSequence (fun k ↦
    arithmeticZeroInfinityNormalizedRetainedUnionRestriction hπ data H k hj u hu b)

/-- The independent attached targets with their original pair and retained-node quotient maps. -/
def arithmeticZeroInfinityNormalizedRetainedTargetSystem : ℕ ⥤ Scheme :=
  Functor.ofSequence (fun k ↦
    arithmeticZeroInfinityNormalizedRetainedTargetRestriction hπ data H k hj u hu b)

local notation "X" => arithmeticZeroInfinityNormalizedRetainedUnionSystem hπ data H hj u hu b
local notation "Y" => arithmeticZeroInfinityNormalizedRetainedTargetSystem hπ data H hj u hu b

/-- The entire actual comparison is natural for the full original arithmetic quotients. -/
def arithmeticZeroInfinityNormalizedRetainedComparisonSystem : X ⟶ Y :=
  NatTrans.ofSequence (fun k ↦ (F k).hom) (by
    intro k
    simpa only [arithmeticZeroInfinityNormalizedRetainedUnionSystem,
      arithmeticZeroInfinityNormalizedRetainedTargetSystem, Functor.ofSequence_obj,
      Functor.ofSequence_map_homOfLE_succ] using
      arithmeticZeroInfinityNormalizedRetainedComparison_restriction hπ data H k hj u hu b)

/-- The entire four-chart comparison is a natural isomorphism at every arithmetic order. -/
def arithmeticZeroInfinityNormalizedRetainedComparisonSystemIso : X ≅ Y :=
  NatIso.ofComponents F (fun {_ _} f ↦
    (arithmeticZeroInfinityNormalizedRetainedComparisonSystem hπ data H hj u hu b).naturality f)

/-- The actual original retained union system has its original global coefficient projection. -/
def arithmeticZeroInfinityNormalizedRetainedUnionSystemStructure : X ⟶ baseSystem R π :=
  NatTrans.ofSequence (fun k ↦ (V k).ι ≫ B k) (by
    intro k
    simpa only [arithmeticZeroInfinityNormalizedRetainedUnionSystem, baseSystem,
      Functor.ofSequence_obj, Functor.ofSequence_map_homOfLE_succ, Category.assoc] using
      arithmeticZeroInfinityNormalizedRetainedUnionRestriction_base hπ data H k hj u hu b)

/-- The independent attached target system retains the original full coefficient base. -/
def arithmeticZeroInfinityNormalizedRetainedTargetSystemStructure : Y ⟶ baseSystem R π :=
  NatTrans.ofSequence p (by
    intro k
    simpa only [arithmeticZeroInfinityNormalizedRetainedTargetSystem, baseSystem,
      Functor.ofSequence_obj, Functor.ofSequence_map_homOfLE_succ] using
      arithmeticZeroInfinityNormalizedRetainedTargetRestriction_base hπ data H k hj u hu b)

/-- The complete natural attached comparison preserves the original base system. -/
theorem arithmeticZeroInfinityNormalizedRetainedComparisonSystem_base :
    arithmeticZeroInfinityNormalizedRetainedComparisonSystem hπ data H hj u hu b ≫
      arithmeticZeroInfinityNormalizedRetainedTargetSystemStructure hπ data H hj u hu b =
        arithmeticZeroInfinityNormalizedRetainedUnionSystemStructure hπ data H hj u hu b := by
  ext k : 2
  exact arithmeticZeroInfinityNormalizedRetainedComparison_base hπ data H k hj u hu b

/-- Nonconsecutive arithmetic orders retain the full attached comparison square. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedComparisonSystem_naturality
    {i j : ℕ} (hij : i ≤ j) :
    (X).map (homOfLE hij) ≫ (F j).hom = (F i).hom ≫ (Y).map (homOfLE hij) :=
  (arithmeticZeroInfinityNormalizedRetainedComparisonSystem hπ data H hj u hu b).naturality _

end FLT.Mazur.WeierstrassDividedDepth
