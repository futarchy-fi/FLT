/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOneInfinityNormalizedRetainedGluing

/-!
# The two complete retained attachments meet in exactly the full common pair

The two original retained nodes are disjoint. Consequently gluing either to
the actual initial/infinity union creates no additional common points.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticOneFiniteAtlasIso simultaneousTwistedArithmeticIso
  arithmeticOneFiniteInitialIso arithmeticInitialFactorRatioChart
  arithmeticOneDiagonalAtlasChart arithmeticOneInfinityNormalizedRetainedToGlobal
  arithmeticOneInfinityNormalizedRetainedSide arithmeticOneInfinityNormalizedRetainedToUnion
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "c" => arithmeticOneDiagonalAtlasChart hπ data H m hj u hu
local notation "U" => arithmeticOneInfinityNormalizedFullUnion hπ data H m hj u hu
local notation "w" => arithmeticOneInfinityNormalizedRetainedToUnion hπ data H m hj u hu
local notation "r" => arithmeticOneInfinityNormalizedRetainedSide hπ data H m hj u hu
local notation "g" => arithmeticOneInfinityNormalizedRetainedToGlobal hπ data H m hj u hu
local notation "a" => fun b ↦ pushout.inl (w b) (r b)

/-- The entire opposite retained attachment meets the first attachment only in the full pair. -/
theorem arithmeticOneInfinityNormalizedRetainedPair_preimage :
    g true ⁻¹' Set.range (g false) = Set.range (a true) := by
  ext x
  constructor
  · intro hx
    rcases SchemeOpenPushout.charts_cover (w true) (r true) x with ⟨z, rfl⟩ | ⟨z, rfl⟩
    · exact ⟨z, rfl⟩
    · have hz : c (.retained ⟨0, by omega⟩ true) z ∈ Set.range (g false) := by
        change (pushout.inr (w true) (r true) ≫ g true) z ∈ Set.range (g false) at hx
        rwa [arithmeticOneInfinityNormalizedRetainedToGlobal_retained] at hx
      rw [arithmeticOneInfinityNormalizedRetainedToGlobal_range] at hz
      rcases hz with hz | hz
      · have hr : z ∈ Set.range (r true) := by
          rw [← arithmeticOneInfinityNormalizedRetained_union_preimage hπ data H m hj u hu true]
          exact hz
        obtain ⟨o, rfl⟩ := hr
        have hc : w true ≫ a true = r true ≫ pushout.inr (w true) (r true) := pushout.condition
        exact ⟨w true o, congrArg (fun f ↦ f o) hc⟩
      · exact False.elim (Set.disjoint_left.mp
          (arithmeticOneDiagonalAtlas_retained_disjoint hπ data H m hj u hu) hz ⟨z, rfl⟩)
  · rintro ⟨z, rfl⟩
    refine ⟨a false z, ?_⟩
    change (a false ≫ g false) z = (a true ≫ g true) z
    rw [arithmeticOneInfinityNormalizedRetainedToGlobal_pair,
      arithmeticOneInfinityNormalizedRetainedToGlobal_pair]

/-- Both entire retained attachments have the original full pair as their scheme fiber product. -/
theorem arithmeticOneInfinityNormalizedRetainedPair_isPullback :
    IsPullback (a false) (a true) (g false) (g true) := by
  apply IsOpenImmersion.isPullback _ _ _ _
  · rw [arithmeticOneInfinityNormalizedRetainedToGlobal_pair,
      arithmeticOneInfinityNormalizedRetainedToGlobal_pair]
  · exact TopologicalSpace.Opens.ext
      (arithmeticOneInfinityNormalizedRetainedPair_preimage hπ data H m hj u hu)

end FLT.Mazur.WeierstrassDividedDepth
