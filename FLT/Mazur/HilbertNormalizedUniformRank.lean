/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertNormalizedFrameAction
public import FLT.Mazur.AffineHilbertDerivedNoetherianRelation
public import FLT.Mazur.EquivalenceRelationCompleteExactRank
public import FLT.Mazur.EquivalenceRelationFiniteCompleteInterior

/-!
# A constructed uniform cutoff for original Hilbert frame completeness

Noetherianity of the selected original affine Hilbert source and compactness of
the full relation construct one rank cutoff. Every normalized frame at or above
it is complete, before choosing any invariant open, scalar map, or boundary prime.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] EquivalenceRelationNormalizedFrames.source
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => Over.Hom.left (AffineRestriction.fst f hL d V c k)
local notation "q" => Over.Hom.left (AffineRestriction.snd f hL d V c k)
local instance uniformRankOver_etale : Etale (Over.mk p).hom := inferInstanceAs (Etale p)
local instance uniformRankOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)
local instance uniformRankOver_compact : QuasiCompact (Over.mk p).hom :=
  inferInstanceAs (QuasiCompact p)

/-- The original geometry supplies a uniform finite bound on all full relation frames. -/
theorem originalFrameRank_exists :
    ∃ N : ℕ, ∀ (x : A.left) (m : ℕ), x ∈ rankImageOpen (Over.mk p) m → m ≤ N := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  exact exists_uniform_rank_bound (Over.mk p)

/-- A rank bound derived from the full original relation, independent of normalized charts. -/
def originalFrameRankCutoff : ℕ := by
  classical
  exact Nat.find (originalFrameRank_exists f hL d V c k)

/-- Every original distinct frame obeys the constructed uniform bound. -/
theorem originalFrameRankCutoff_spec (x : A.left) (m : ℕ)
    (hx : x ∈ rankImageOpen (Over.mk p) m) :
    m ≤ originalFrameRankCutoff f hL d V c k := by
  classical
  exact Nat.find_spec (originalFrameRank_exists f hL d V c k) x m hx

/-- No smaller bound controls all full original frame images. -/
theorem originalFrameRankCutoff_minimal (M : ℕ)
    (hM : ∀ (x : A.left) (m : ℕ), x ∈ rankImageOpen (Over.mk p) m → m ≤ M) :
    originalFrameRankCutoff f hL d V c k ≤ M := by
  classical
  exact Nat.find_min' (originalFrameRank_exists f hL d V c k) hM

/-- A positive cutoff is attained by an actual original frame, so it is not an empty bound. -/
theorem originalFrameRankCutoff_attained
    (hN : 0 < originalFrameRankCutoff f hL d V c k) :
    ∃ x : A.left, x ∈ rankImageOpen (Over.mk p) (originalFrameRankCutoff f hL d V c k) := by
  classical
  let N := originalFrameRankCutoff f hL d V c k
  have hmin : ¬ ∀ (x : A.left) (m : ℕ),
      x ∈ rankImageOpen (Over.mk p) m → m ≤ N - 1 := by
    intro h
    have hm := originalFrameRankCutoff_minimal f hL d V c k (N - 1) h
    omega
  push Not at hmin
  obtain ⟨x, m, hx, hm⟩ := hmin
  exact ⟨x, rankImageOpen_antitone (Over.mk p) (by omega : N ≤ m) hx⟩

/-- A nonempty original Hilbert source has a positive full-relation rank cutoff. -/
theorem originalFrameRankCutoff_pos [Nonempty A.left] :
    0 < originalFrameRankCutoff f hL d V c k := by
  obtain ⟨m, o, y, _, _⟩ := exists_complete_normalized_point
    (fullRelationSchemeEquivalence f hL d V c k) (Classical.ofNonempty : A.left)
  have hm := originalFrameRankCutoff_spec f hL d V c k (first p q (Fin m) o y) m
    ⟨inclusion p q (Fin m) o y, rfl⟩
  exact (lt_of_le_of_lt (Nat.zero_le o.val) o.isLt).trans_le hm

/-- The maximal size actually has a complete normalized point on every nonempty original source. -/
theorem exists_normalized_point_at_rankCutoff [Nonempty A.left] :
    ∃ (o : Fin (originalFrameRankCutoff f hL d V c k))
      (y : normalizedFullRelationFrames f hL d V c k
        (originalFrameRankCutoff f hL d V c k) o),
      y ∈ completePointLocus («p» := p) («q» := q)
        (Fin (originalFrameRankCutoff f hL d V c k)) o := by
  obtain ⟨x, hx⟩ := originalFrameRankCutoff_attained f hL d V c k
    (originalFrameRankCutoff_pos f hL d V c k)
  obtain ⟨m, o, y, hy, hc⟩ := exists_complete_normalized_point
    (fullRelationSchemeEquivalence f hL d V c k) x
  have hm := originalFrameRankCutoff_spec f hL d V c k (first p q (Fin m) o y) m
    ⟨inclusion p q (Fin m) o y, rfl⟩
  have hN : originalFrameRankCutoff f hL d V c k ≤ m := by
    by_contra h
    have hr := hc
    rw [completePointLocus_eq_rankAtMost_preimage] at hr
    change first p q (Fin m) o y ∈ rankAtMost (Over.mk p) m at hr
    rw [hy] at hr
    exact hr (rankImageOpen_antitone (Over.mk p) (Nat.lt_of_not_ge h) hx)
  obtain rfl := Nat.le_antisymm hm hN
  exact ⟨o, y, hc⟩

/-- At or above the cutoff, every actual normalized original frame is complete. -/
theorem normalizedFullRelation_complete_of_cutoff (n : ℕ) (o : Fin n)
    (hn : originalFrameRankCutoff f hL d V c k ≤ n)
    (x : normalizedFullRelationFrames f hL d V c k n o) :
    x ∈ completePointLocus («p» := p) («q» := q) (Fin n) o := by
  rw [completePointLocus_eq_rankAtMost_preimage]
  intro hx
  exact Nat.not_succ_le_self n ((originalFrameRankCutoff_spec f hL d V c k _ _ hx).trans hn)

/-- Sizes strictly exceeding the cutoff have no original normalized points at all. -/
theorem normalizedFullRelation_isEmpty_above_cutoff (n : ℕ) (o : Fin n)
    (hn : originalFrameRankCutoff f hL d V c k < n) :
    IsEmpty (normalizedFullRelationFrames f hL d V c k n o) := by
  refine ⟨fun x ↦ ?_⟩
  apply Nat.not_le_of_lt hn
  apply originalFrameRankCutoff_spec f hL d V c k (first p q (Fin n) o x) n
  refine ⟨inclusion p q (Fin n) o x, ?_⟩
  rfl

/-- An incomplete frame must have one of the finitely many sizes below the original cutoff. -/
theorem normalizedFullRelation_incomplete_size_lt (n : ℕ) (o : Fin n)
    (x : normalizedFullRelationFrames f hL d V c k n o)
    (hx : x ∉ completePointLocus («p» := p) («q» := q) (Fin n) o) :
    n < originalFrameRankCutoff f hL d V c k := by
  by_contra hn
  exact hx (normalizedFullRelation_complete_of_cutoff f hL d V c k n o
    (Nat.le_of_not_gt hn) x)

end FLT.Mazur.HilbertChart.AffineRestriction
