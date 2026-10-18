/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroDiagonalAtlasSeparation
public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedRetainedSide

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
  arithmeticZeroFiniteAtlasIso simultaneousTwistedArithmeticIso
  arithmeticZeroFiniteInitialIso arithmeticInitialFactorRatioChart

/-- Disjoint chart images give an empty full inverse image. -/
theorem fullChart_disjoint_preimage {A B X : Scheme} {f : A ⟶ X} {g : B ⟶ X}
    (h : Disjoint (Set.range f) (Set.range g)) : f ⁻¹' Set.range g = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact Set.disjoint_left.mp h ⟨x, rfl⟩ hx

/-- Reparameterizing a full chart by an isomorphism preserves its complete image. -/
theorem fullChart_iso_comp_range {A B X : Scheme} (e : A ≅ B) (f : B ⟶ X) :
    Set.range (e.hom ≫ f) = Set.range f := e.hom.homeomorph.surjective.range_comp f

variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "D" => arithmeticZeroDiagonalState hπ data H 0 hj u hu
local notation "s" => PolygonArithmeticSimultaneous.State.last D m
local notation "c" => arithmeticZeroDiagonalAtlasChart hπ data H m hj u hu
local notation "U" => arithmeticZeroInfinityNormalizedFullUnion hπ data H m hj u hu
local notation "w" => arithmeticZeroInfinityNormalizedRetainedToUnion hπ data H m hj u hu
local notation "r" => arithmeticZeroInfinityNormalizedRetainedSide hπ data H m hj u hu
local notation "B" => punctureSpecIso (arithmeticInitialBaseEquiv data H m 0 hj)

/-- The actual full union consists of infinity and the two entire original initial opens. -/
theorem arithmeticZeroInfinityNormalizedFullUnion_range :
    Set.range (U).ι =
      (Set.range (c .infinity) ∪ Set.range (c (.initial false))) ∪
        (Set.range (c .infinity) ∪ Set.range (c (.initial true))) := by
  rw [Scheme.Opens.range_ι]
  rfl

/-- The whole retained preimage of its same-label initial chart is the full right branch. -/
theorem arithmeticZeroInfinityNormalizedRetained_initial_preimage (b : Bool) :
    c (.retained ⟨0, by omega⟩ b) ⁻¹' Set.range (c (.initial b)) =
      Set.range (rightBranchOpen Q (s b)) := by
  calc
    _ = Set.range ((B).hom ≫ rightBranchOpen Q (s b)) :=
      fullNodePullback_preimage
        (arithmeticZeroDiagonalAtlas_initial_isPullback hπ data H m hj u hu b)
    _ = _ := fullChart_iso_comp_range B (rightBranchOpen Q (s b))

/-- The entire three-chart union has exactly the prescribed full retained attachment. -/
theorem arithmeticZeroInfinityNormalizedRetained_union_preimage (b : Bool) :
    c (.retained ⟨0, by omega⟩ b) ⁻¹' Set.range (U).ι = Set.range (r b) := by
  rw [arithmeticZeroInfinityNormalizedFullUnion_range,
    Set.preimage_union, Set.preimage_union, Set.preimage_union,
    fullChart_disjoint_preimage
      (arithmeticZeroDiagonalAtlas_retained_infinity_disjoint hπ data H m hj u hu b),
    Set.empty_union, Set.empty_union, arithmeticZeroInfinityNormalizedRetainedSide_range]
  cases b
  · rw [fullChart_disjoint_preimage
      (arithmeticZeroDiagonalAtlas_initial_crossLabel_disjoint hπ data H m hj u hu
        true false (by decide)).symm, Set.union_empty,
      arithmeticZeroInfinityNormalizedRetained_initial_preimage]
  · rw [fullChart_disjoint_preimage
      (arithmeticZeroDiagonalAtlas_initial_crossLabel_disjoint hπ data H m hj u hu
        false true Bool.false_ne_true).symm, Set.empty_union,
      arithmeticZeroInfinityNormalizedRetained_initial_preimage]

/-- The exact full source attachment is the scheme intersection with the entire retained node. -/
theorem arithmeticZeroInfinityNormalizedRetained_isPullback (b : Bool) :
    IsPullback (w b) (r b) (U).ι (c (.retained ⟨0, by omega⟩ b)) := by
  apply IsOpenImmersion.isPullback _ _ _ _
  · exact arithmeticZeroInfinityNormalizedRetainedSide_global hπ data H m hj u hu b
  · exact TopologicalSpace.Opens.ext
      (arithmeticZeroInfinityNormalizedRetained_union_preimage hπ data H m hj u hu b)

/-- The original common terminal misses the whole normalized source pair. -/
theorem arithmeticZeroInfinityNormalizedFullUnion_terminal_disjoint :
    Disjoint (Set.range (U).ι) (Set.range (c .terminal)) := by
  rw [arithmeticZeroInfinityNormalizedFullUnion_range]
  simp only [Set.disjoint_union_left]
  exact ⟨⟨(arithmeticZeroDiagonalAtlas_terminal_infinity_disjoint hπ data H m hj u hu).symm,
    arithmeticZeroDiagonalAtlas_initial_terminal_disjoint hπ data H m hj u hu false⟩,
    ⟨(arithmeticZeroDiagonalAtlas_terminal_infinity_disjoint hπ data H m hj u hu).symm,
    arithmeticZeroDiagonalAtlas_initial_terminal_disjoint hπ data H m hj u hu true⟩⟩

end FLT.Mazur.WeierstrassDividedDepth
