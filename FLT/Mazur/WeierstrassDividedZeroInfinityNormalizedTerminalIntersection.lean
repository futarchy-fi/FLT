/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedRetainedPairSystem

/-!
# The complete remaining terminal intersection

The five-chart source misses the terminal except at its two original closing
punctures. Those punctures are disjoint, and adding the full terminal covers
the entire original arithmetic stage.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFiniteAtlasIso simultaneousTwistedArithmeticIso
  arithmeticZeroFiniteInitialIso arithmeticInitialFactorRatioChart
  arithmeticZeroDiagonalAtlasChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "c" => arithmeticZeroDiagonalAtlasChart hπ data H m hj u hu
local notation "U" => arithmeticZeroInfinityNormalizedFullUnion hπ data H m hj u hu
local notation "V" => arithmeticZeroInfinityNormalizedRetainedPairUnion hπ data H m hj u hu
local notation "D" => arithmeticZeroDiagonalState hπ data H 0 hj u hu
local notation "t" => PolygonArithmeticSimultaneous.State.terminal D m

/-- The full five-chart source contains precisely the pair and both original retained nodes. -/
theorem arithmeticZeroInfinityNormalizedRetainedPairUnion_range :
    Set.range (V).ι =
      (Set.range (U).ι ∪ Set.range (c (.retained ⟨0, by omega⟩ false))) ∪
        (Set.range (U).ι ∪ Set.range (c (.retained ⟨0, by omega⟩ true))) := by
  simp only [Scheme.Opens.range_ι]
  rfl

/-- Each entire retained node meets the original terminal in its full closing puncture. -/
theorem arithmeticZeroInfinityNormalizedTerminal_retained_preimage (b : Bool) :
    c .terminal ⁻¹' Set.range (c (.retained ⟨0, by omega⟩ b)) =
      Set.range (punctureOpen t b) :=
  fullNodePullback_preimage
    (arithmeticZeroDiagonalAtlas_closing_isPullback hπ data H m hj u hu b)

/-- The entire remaining terminal intersection is exactly the two original closing punctures. -/
theorem arithmeticZeroInfinityNormalizedTerminal_pair_preimage :
    c .terminal ⁻¹' Set.range (V).ι =
      Set.range (punctureOpen t false) ∪ Set.range (punctureOpen t true) := by
  rw [arithmeticZeroInfinityNormalizedRetainedPairUnion_range,
    Set.preimage_union, Set.preimage_union, Set.preimage_union,
    fullChart_disjoint_preimage
      (arithmeticZeroInfinityNormalizedFullUnion_terminal_disjoint hπ data H m hj u hu).symm,
    Set.empty_union, Set.empty_union,
    arithmeticZeroInfinityNormalizedTerminal_retained_preimage,
    arithmeticZeroInfinityNormalizedTerminal_retained_preimage]

/-- The two entire terminal punctures are disjoint over the unreduced arithmetic base. -/
theorem arithmeticZeroInfinityNormalizedTerminal_punctures_disjoint :
    Disjoint (Set.range (punctureOpen t false)) (Set.range (punctureOpen t true)) := by
  rw [← arithmeticZeroInfinityNormalizedTerminal_retained_preimage hπ data H m hj u hu false,
    ← arithmeticZeroInfinityNormalizedTerminal_retained_preimage hπ data H m hj u hu true]
  exact Disjoint.preimage _
    (arithmeticZeroDiagonalAtlas_retained_disjoint hπ data H m hj u hu)

/-- Adding the whole common terminal to the five-chart union covers the original stage. -/
theorem arithmeticZeroInfinityNormalizedTerminal_pair_cover
    (z : simultaneousTwistedArithmeticStage hπ data H m 0 hj u hu) :
    (∃ x, (V).ι x = z) ∨ ∃ y, c .terminal y = z := by
  obtain ⟨i, x, rfl⟩ := arithmeticZeroDiagonalAtlas_cover hπ data H m hj u hu z
  cases i with
  | terminal => exact Or.inr ⟨x, rfl⟩
  | infinity =>
    apply Or.inl
    change c .infinity x ∈ Set.range (V).ι
    rw [arithmeticZeroInfinityNormalizedRetainedPairUnion_range]
    left; left
    rw [arithmeticZeroInfinityNormalizedFullUnion_range]
    exact Or.inl (Or.inl ⟨x, rfl⟩)
  | initial b =>
    apply Or.inl
    change c (.initial b) x ∈ Set.range (V).ι
    rw [arithmeticZeroInfinityNormalizedRetainedPairUnion_range]
    left; left
    rw [arithmeticZeroInfinityNormalizedFullUnion_range]
    cases b
    · exact Or.inl (Or.inr ⟨x, rfl⟩)
    · exact Or.inr (Or.inr ⟨x, rfl⟩)
  | retained i b =>
    have hi : i = ⟨0, by omega⟩ := Fin.eq_zero i
    subst i
    apply Or.inl
    change c (.retained ⟨0, by omega⟩ b) x ∈ Set.range (V).ι
    rw [arithmeticZeroInfinityNormalizedRetainedPairUnion_range]
    cases b
    · exact Or.inl (Or.inr ⟨x, rfl⟩)
    · exact Or.inr (Or.inr ⟨x, rfl⟩)

end FLT.Mazur.WeierstrassDividedDepth
