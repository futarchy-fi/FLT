/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedRetainedPairUnionRestriction

/-!
# The full exact retained attachment as an arithmetic quotient system

The whole actual five-chart union and independent doubly attached target
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
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "V" => fun k ↦
  arithmeticZeroInfinityNormalizedRetainedPairUnion hπ data H k hj u hu
local notation "F" => fun k ↦
  arithmeticZeroInfinityNormalizedRetainedPairComparison hπ data H k hj u hu
local notation "B" => fun k ↦ arithmeticZeroDiagonalSourceToBase hπ data H k hj u hu
local notation "p" => fun k ↦
  arithmeticZeroInfinityNormalizedRetainedPairTargetToBase hπ data H k hj u hu

/-- The whole actual five-chart unions with their original global quotient restrictions. -/
def arithmeticZeroInfinityNormalizedRetainedPairUnionSystem : ℕ ⥤ Scheme :=
  Functor.ofSequence (fun k ↦
    arithmeticZeroInfinityNormalizedRetainedPairUnionRestriction hπ data H k hj u hu)

/-- The independent attached targets with their original pair and retained-node quotient maps. -/
def arithmeticZeroInfinityNormalizedRetainedPairTargetSystem : ℕ ⥤ Scheme :=
  Functor.ofSequence (fun k ↦
    arithmeticZeroInfinityNormalizedRetainedPairTargetRestriction hπ data H k hj u hu)

local notation "X" => arithmeticZeroInfinityNormalizedRetainedPairUnionSystem hπ data H hj u hu
local notation "Y" => arithmeticZeroInfinityNormalizedRetainedPairTargetSystem hπ data H hj u hu

/-- The entire actual comparison is natural for the full original arithmetic quotients. -/
def arithmeticZeroInfinityNormalizedRetainedPairComparisonSystem : X ⟶ Y :=
  NatTrans.ofSequence (fun k ↦ (F k).hom) (by
    intro k
    simpa only [arithmeticZeroInfinityNormalizedRetainedPairUnionSystem,
      arithmeticZeroInfinityNormalizedRetainedPairTargetSystem, Functor.ofSequence_obj,
      Functor.ofSequence_map_homOfLE_succ] using
      arithmeticZeroInfinityNormalizedRetainedPairComparison_restriction hπ data H k hj u hu)

/-- The entire five-chart comparison is a natural isomorphism at every arithmetic order. -/
def arithmeticZeroInfinityNormalizedRetainedPairComparisonSystemIso : X ≅ Y :=
  NatIso.ofComponents F (fun {_ _} f ↦
    (arithmeticZeroInfinityNormalizedRetainedPairComparisonSystem hπ data H hj u hu).naturality f)

/-- The actual original retained union system has its original global coefficient projection. -/
def arithmeticZeroInfinityNormalizedRetainedPairUnionSystemStructure : X ⟶ baseSystem R π :=
  NatTrans.ofSequence (fun k ↦ (V k).ι ≫ B k) (by
    intro k
    simpa only [arithmeticZeroInfinityNormalizedRetainedPairUnionSystem, baseSystem,
      Functor.ofSequence_obj, Functor.ofSequence_map_homOfLE_succ, Category.assoc] using
      arithmeticZeroInfinityNormalizedRetainedPairUnionRestriction_base hπ data H k hj u hu)

/-- The independent attached target system retains the original full coefficient base. -/
def arithmeticZeroInfinityNormalizedRetainedPairTargetSystemStructure : Y ⟶ baseSystem R π :=
  NatTrans.ofSequence p (by
    intro k
    simpa only [arithmeticZeroInfinityNormalizedRetainedPairTargetSystem, baseSystem,
      Functor.ofSequence_obj, Functor.ofSequence_map_homOfLE_succ] using
      arithmeticZeroInfinityNormalizedRetainedPairTargetRestriction_base hπ data H k hj u hu)

/-- The complete natural attached comparison preserves the original base system. -/
theorem arithmeticZeroInfinityNormalizedRetainedPairComparisonSystem_base :
    arithmeticZeroInfinityNormalizedRetainedPairComparisonSystem hπ data H hj u hu ≫
      arithmeticZeroInfinityNormalizedRetainedPairTargetSystemStructure hπ data H hj u hu =
        arithmeticZeroInfinityNormalizedRetainedPairUnionSystemStructure hπ data H hj u hu := by
  ext k : 2
  exact arithmeticZeroInfinityNormalizedRetainedPairComparison_base hπ data H k hj u hu

/-- Nonconsecutive arithmetic orders retain the full attached comparison square. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedPairComparisonSystem_naturality
    {i j : ℕ} (hij : i ≤ j) :
    (X).map (homOfLE hij) ≫ (F j).hom = (F i).hom ≫ (Y).map (homOfLE hij) :=
  (arithmeticZeroInfinityNormalizedRetainedPairComparisonSystem hπ data H hj u hu).naturality _

end FLT.Mazur.WeierstrassDividedDepth
