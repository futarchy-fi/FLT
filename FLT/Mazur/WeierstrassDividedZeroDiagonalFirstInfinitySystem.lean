/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroDiagonalFirstInfinityRestriction

/-!
# The actual first initial/infinity union as an arithmetic quotient system

The restriction is identified with the original global arrow, and the full
union-to-polygon comparison is natural at every pair of arithmetic orders.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFiniteInitialIso arithmeticInitialFactorRatioChart
  arithmeticZeroFiniteAtlasIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "U" => fun k ↦ arithmeticZeroDiagonalFirstInfinityUnion hπ data H k hj u hu
local notation "E" => fun k ↦ arithmeticZeroDiagonalFirstInfinityUnionIso hπ data H k hj u hu
local notation "N" => fun k ↦ arithmeticZeroDiagonalFirstInfinityUnionNodeMap hπ data H k hj u hu
local notation "F" => fun k ↦ arithmeticZeroDiagonalFirstInfinityUnionComparison hπ data H k hj u hu
local notation "q" => simultaneousTwistedArithmeticRestriction hπ data H m 0 hj u hu

/-- The actual full source open union inherits the original complete quotient arrow. -/
def arithmeticZeroDiagonalFirstInfinityUnionRestriction :
    (U m).toScheme ⟶ (U (m + 1)).toScheme :=
  (E m).inv ≫ arithmeticZeroDiagonalFirstInfinityRestriction hπ data H m hj u hu ≫
    (E (m + 1)).hom

local notation "r" => arithmeticZeroDiagonalFirstInfinityUnionRestriction hπ data H m hj u hu

/-- The actual union quotient recovers the complete pushout quotient. -/
@[reassoc] theorem arithmeticZeroDiagonalFirstInfinityUnionRestriction_transport :
    (E m).hom ≫ r =
      arithmeticZeroDiagonalFirstInfinityRestriction hπ data H m hj u hu ≫
        (E (m + 1)).hom := by
  rw [arithmeticZeroDiagonalFirstInfinityUnionRestriction, Iso.hom_inv_id_assoc]

/-- The open-union restriction is exactly the original global arithmetic arrow. -/
@[reassoc] theorem arithmeticZeroDiagonalFirstInfinityUnionRestriction_global :
    r ≫ (U (m + 1)).ι = (U m).ι ≫ q := by
  apply (cancel_epi (E m).hom).mp
  rw [arithmeticZeroDiagonalFirstInfinityUnionRestriction_transport_assoc,
    arithmeticZeroDiagonalFirstInfinityUnionIso_global,
    arithmeticZeroDiagonalFirstInfinityRestriction_global,
    arithmeticZeroDiagonalFirstInfinityUnionIso_global_assoc]

/-- The full union-node isomorphism follows the actual diagonal node coefficient map. -/
@[reassoc] theorem arithmeticZeroDiagonalFirstInfinityUnionNodeMap_restriction :
    r ≫ N (m + 1) = N m ≫
      arithmeticZeroDiagonalInitialNodeRestriction hπ data H 0 hj u hu m false := by
  apply (cancel_epi (E m).hom).mp
  rw [arithmeticZeroDiagonalFirstInfinityUnionRestriction_transport_assoc,
    arithmeticZeroDiagonalFirstInfinityUnionNodeMap_transport,
    arithmeticZeroDiagonalFirstInfinityRestriction_node,
    arithmeticZeroDiagonalFirstInfinityUnionNodeMap_transport_assoc]

/-- The complete partial polygon comparison follows both original arithmetic quotients. -/
@[reassoc] theorem arithmeticZeroDiagonalFirstInfinityUnionComparison_restriction :
    r ≫ F (m + 1) = F m ≫ arithmeticZeroDiagonalPolygonRestriction hπ data H m hj u hu := by
  simp only [arithmeticZeroDiagonalFirstInfinityUnionComparison, Category.assoc,
    arithmeticZeroDiagonalPolygonInitialMap_restriction]
  rw [← Category.assoc, arithmeticZeroDiagonalFirstInfinityUnionNodeMap_restriction,
    Category.assoc]

/-- The actual complete initial/infinity unions form a source quotient system. -/
def arithmeticZeroDiagonalFirstInfinityUnionSystem : ℕ ⥤ Scheme :=
  Functor.ofSequence (fun k ↦
    arithmeticZeroDiagonalFirstInfinityUnionRestriction hπ data H k hj u hu)

/-- The full source union embeds naturally in the original global arithmetic system. -/
def arithmeticZeroDiagonalFirstInfinityUnionSystemInclusion :
    arithmeticZeroDiagonalFirstInfinityUnionSystem hπ data H hj u hu ⟶
      changedArithmeticTargetSystem hπ data H 0 hj u hu :=
  NatTrans.ofSequence (fun k ↦ (U k).ι) (by
    intro k
    simpa only [arithmeticZeroDiagonalFirstInfinityUnionSystem, changedArithmeticTargetSystem,
      Functor.ofSequence_obj, Functor.ofSequence_map_homOfLE_succ] using
      arithmeticZeroDiagonalFirstInfinityUnionRestriction_global hπ data H k hj u hu)

/-- The constructed full source-union comparison is a morphism of quotient systems. -/
def arithmeticZeroDiagonalFirstInfinityUnionSystemComparison :
    arithmeticZeroDiagonalFirstInfinityUnionSystem hπ data H hj u hu ⟶
      arithmeticZeroDiagonalPolygonSystem hπ data H hj u hu :=
  NatTrans.ofSequence (fun k ↦ F k) (by
    intro k
    simpa only [arithmeticZeroDiagonalFirstInfinityUnionSystem,
      arithmeticZeroDiagonalPolygonSystem, Functor.ofSequence_obj,
      Functor.ofSequence_map_homOfLE_succ] using
      arithmeticZeroDiagonalFirstInfinityUnionComparison_restriction hπ data H k hj u hu)

/-- All nonconsecutive arithmetic orders retain the full original source-union comparison. -/
@[reassoc] theorem arithmeticZeroDiagonalFirstInfinityUnionComparison_naturality
    {a b : ℕ} (hab : a ≤ b) :
    (arithmeticZeroDiagonalFirstInfinityUnionSystem hπ data H hj u hu).map (homOfLE hab) ≫ F b =
      F a ≫ (arithmeticZeroDiagonalPolygonSystem hπ data H hj u hu).map (homOfLE hab) :=
  (arithmeticZeroDiagonalFirstInfinityUnionSystemComparison hπ data H hj u hu).naturality
    (homOfLE hab)

end FLT.Mazur.WeierstrassDividedDepth
