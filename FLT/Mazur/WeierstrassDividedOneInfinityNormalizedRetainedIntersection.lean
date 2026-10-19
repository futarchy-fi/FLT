/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOneDiagonalAtlasSeparation
public import FLT.Mazur.WeierstrassDividedOneInfinityNormalizedRetainedSide
public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedRetainedIntersection

/-!
# The full normalized pair meets each retained node in its exact attachment

The original infinity and opposite initial charts miss the whole retained node.
The same-label original pullback therefore computes the entire intersection.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticOneFiniteAtlasIso simultaneousTwistedArithmeticIso
  arithmeticOneFiniteInitialIso arithmeticInitialFactorRatioChart

variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "D" => arithmeticOneDiagonalState hπ data H hj u hu
local notation "s" => PolygonArithmeticRetainedChain.State.retained D m 0
local notation "c" => arithmeticOneDiagonalAtlasChart hπ data H m hj u hu
local notation "U" => arithmeticOneInfinityNormalizedFullUnion hπ data H m hj u hu
local notation "w" => arithmeticOneInfinityNormalizedRetainedToUnion hπ data H m hj u hu
local notation "r" => arithmeticOneInfinityNormalizedRetainedSide hπ data H m hj u hu
local notation "B" => punctureSpecIso (arithmeticInitialBaseEquiv data H m 1 hj)

/-- The actual full union consists of infinity and the two entire original initial opens. -/
theorem arithmeticOneInfinityNormalizedFullUnion_range :
    Set.range (U).ι =
      (Set.range (c .infinity) ∪ Set.range (c (.initial false))) ∪
        (Set.range (c .infinity) ∪ Set.range (c (.initial true))) := by
  rw [Scheme.Opens.range_ι]
  rfl

/-- The whole retained preimage of its same-label initial chart is the full right branch. -/
theorem arithmeticOneInfinityNormalizedRetained_initial_preimage (b : Bool) :
    c (.retained ⟨0, by omega⟩ b) ⁻¹' Set.range (c (.initial b)) =
      Set.range (rightBranchOpen Q (s b)) := by
  calc
    _ = Set.range ((B).hom ≫ rightBranchOpen Q (s b)) :=
      fullNodePullback_preimage
        (arithmeticOneDiagonalAtlas_initial_isPullback hπ data H m hj u hu b)
    _ = _ := fullChart_iso_comp_range B (rightBranchOpen Q (s b))

/-- The entire three-chart union has exactly the prescribed full retained attachment. -/
theorem arithmeticOneInfinityNormalizedRetained_union_preimage (b : Bool) :
    c (.retained ⟨0, by omega⟩ b) ⁻¹' Set.range (U).ι = Set.range (r b) := by
  rw [arithmeticOneInfinityNormalizedFullUnion_range,
    Set.preimage_union, Set.preimage_union, Set.preimage_union,
    fullChart_disjoint_preimage
      (arithmeticOneDiagonalAtlas_retained_infinity_disjoint hπ data H m hj u hu b),
    Set.empty_union, Set.empty_union, arithmeticOneInfinityNormalizedRetainedSide_range]
  cases b
  · rw [fullChart_disjoint_preimage
      (arithmeticOneDiagonalAtlas_initial_crossLabel_disjoint hπ data H m hj u hu
        true false (by decide)).symm, Set.union_empty,
      arithmeticOneInfinityNormalizedRetained_initial_preimage]
  · rw [fullChart_disjoint_preimage
      (arithmeticOneDiagonalAtlas_initial_crossLabel_disjoint hπ data H m hj u hu
        false true Bool.false_ne_true).symm, Set.empty_union,
      arithmeticOneInfinityNormalizedRetained_initial_preimage]

/-- The exact full source attachment is the scheme intersection with the entire retained node. -/
theorem arithmeticOneInfinityNormalizedRetained_isPullback (b : Bool) :
    IsPullback (w b) (r b) (U).ι (c (.retained ⟨0, by omega⟩ b)) := by
  apply IsOpenImmersion.isPullback _ _ _ _
  · exact arithmeticOneInfinityNormalizedRetainedSide_global hπ data H m hj u hu b
  · exact TopologicalSpace.Opens.ext
      (arithmeticOneInfinityNormalizedRetained_union_preimage hπ data H m hj u hu b)

/-- The original common terminal misses the whole normalized source pair. -/
theorem arithmeticOneInfinityNormalizedFullUnion_terminal_disjoint :
    Disjoint (Set.range (U).ι) (Set.range (c .terminal)) := by
  rw [arithmeticOneInfinityNormalizedFullUnion_range]
  simp only [Set.disjoint_union_left]
  exact ⟨⟨(arithmeticOneDiagonalAtlas_terminal_infinity_disjoint hπ data H m hj u hu).symm,
    arithmeticOneDiagonalAtlas_initial_terminal_disjoint hπ data H m hj u hu false⟩,
    ⟨(arithmeticOneDiagonalAtlas_terminal_infinity_disjoint hπ data H m hj u hu).symm,
    arithmeticOneDiagonalAtlas_initial_terminal_disjoint hπ data H m hj u hu true⟩⟩

end FLT.Mazur.WeierstrassDividedDepth
