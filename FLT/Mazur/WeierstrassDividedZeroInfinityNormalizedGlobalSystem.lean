/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedGlobalRestriction

/-!
# The complete exact-twist global comparison as an arithmetic quotient system

The whole original arithmetic stage and independently glued exact-twist target
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
local notation "F" => fun k ↦
  arithmeticZeroInfinityNormalizedGlobalComparison hπ data H k hj u hu
local notation "B" => fun k ↦ arithmeticZeroDiagonalSourceToBase hπ data H k hj u hu
local notation "p" => fun k ↦
  arithmeticZeroInfinityNormalizedGlobalTargetToBase hπ data H k hj u hu

/-- The complete independent targets retain their pair and common-terminal quotient maps. -/
def arithmeticZeroInfinityNormalizedGlobalTargetSystem : ℕ ⥤ Scheme :=
  Functor.ofSequence (fun k ↦
    arithmeticZeroInfinityNormalizedGlobalTargetRestriction hπ data H k hj u hu)

local notation "X" => changedArithmeticTargetSystem hπ data H 0 hj u hu
local notation "Y" => arithmeticZeroInfinityNormalizedGlobalTargetSystem hπ data H hj u hu

/-- The entire actual comparison is natural for the full original arithmetic quotients. -/
def arithmeticZeroInfinityNormalizedGlobalComparisonSystem : X ⟶ Y :=
  NatTrans.ofSequence (fun k ↦ (F k).hom) (by
    intro k
    simpa only [changedArithmeticTargetSystem,
      arithmeticZeroInfinityNormalizedGlobalTargetSystem, Functor.ofSequence_obj,
      Functor.ofSequence_map_homOfLE_succ] using
      arithmeticZeroInfinityNormalizedGlobalComparison_restriction hπ data H k hj u hu)

/-- The entire global comparison is a natural isomorphism at every arithmetic order. -/
def arithmeticZeroInfinityNormalizedGlobalComparisonSystemIso : X ≅ Y :=
  NatIso.ofComponents F (fun {_ _} f ↦
    (arithmeticZeroInfinityNormalizedGlobalComparisonSystem hπ data H hj u hu).naturality f)

/-- The entire original stage system has its original global coefficient projection. -/
def arithmeticZeroInfinityNormalizedGlobalSourceSystemStructure : X ⟶ baseSystem R π :=
  NatTrans.ofSequence B (by
    intro k
    simpa only [changedArithmeticTargetSystem, baseSystem,
      Functor.ofSequence_obj, Functor.ofSequence_map_homOfLE_succ, Category.assoc] using
      arithmeticZeroDiagonalSourceToBase_restriction hπ data H k hj u hu)

/-- The independent attached target system retains the original full coefficient base. -/
def arithmeticZeroInfinityNormalizedGlobalTargetSystemStructure : Y ⟶ baseSystem R π :=
  NatTrans.ofSequence p (by
    intro k
    simpa only [arithmeticZeroInfinityNormalizedGlobalTargetSystem, baseSystem,
      Functor.ofSequence_obj, Functor.ofSequence_map_homOfLE_succ] using
      arithmeticZeroInfinityNormalizedGlobalTargetRestriction_base hπ data H k hj u hu)

/-- The complete natural attached comparison preserves the original base system. -/
theorem arithmeticZeroInfinityNormalizedGlobalComparisonSystem_base :
    arithmeticZeroInfinityNormalizedGlobalComparisonSystem hπ data H hj u hu ≫
      arithmeticZeroInfinityNormalizedGlobalTargetSystemStructure hπ data H hj u hu =
        arithmeticZeroInfinityNormalizedGlobalSourceSystemStructure hπ data H hj u hu := by
  ext k : 2
  exact arithmeticZeroInfinityNormalizedGlobalComparison_base hπ data H k hj u hu

/-- Nonconsecutive arithmetic orders retain the full attached comparison square. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedGlobalComparisonSystem_naturality
    {i j : ℕ} (hij : i ≤ j) :
    (X).map (homOfLE hij) ≫ (F j).hom = (F i).hom ≫ (Y).map (homOfLE hij) :=
  (arithmeticZeroInfinityNormalizedGlobalComparisonSystem hπ data H hj u hu).naturality _

end FLT.Mazur.WeierstrassDividedDepth
