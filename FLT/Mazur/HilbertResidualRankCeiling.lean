/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertNormalizedUniformRank
public import FLT.Mazur.HilbertRankStratumOriginalNeighborhoods
public import FLT.Mazur.HilbertCompleteInteriorFiniteCriterion
public import FLT.Mazur.EquivalenceRelationExactRankInterior
public import FLT.Mazur.RelativeFrameSpecializationCeiling

/-!
# Exact original residual ranks and lifting generizations

Every original point has a generization on a proved boundary-lifting open,
with rank equal to the least local ceiling. Outside the original finite locus,
its exact rank is strictly smaller than that ceiling and an actual larger-frame
valuation at that same center cannot extend. The remaining extension problem
is retained, not discharged by density or properness of the original curve.
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
local instance residualCeilingOver_etale : Etale (Over.mk p).hom := inferInstanceAs (Etale p)
local instance residualCeilingOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)
local instance residualCeilingOver_compact : QuasiCompact (Over.mk p).hom :=
  inferInstanceAs (QuasiCompact p)

local notation "e" => fullRelationSchemeEquivalence f hL d V c k
local notation "eo" => equivalence f hL d V c k
local notation "m" => originalClosedInvariantMap f hL d V c k
open SchemeOpenEnvelope RelativeRelationOrbit InvariantOpenRelationDiagram IsLocalRing
local instance residualCeilingQuasiFinite : LocallyQuasiFinite p :=
  LocallyQuasiFinite.of_finite_preimage_singleton _ (fst_finite_fiber f hL d V c k)

/-- The least rank bound on all original generizations of this unchanged Hilbert source point. -/
def originalSpecializationRankCeiling (x : A.left) : ℕ := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  exact specializationRankCeiling (Over.mk p) x

/-- The local original ceiling tests an actual open rank neighborhood. -/
theorem original_rankBound_iff_ceiling (x : A.left) (n : ℕ) :
    x ∈ rankBoundOpen (Over.mk p) n ↔
      originalSpecializationRankCeiling f hL d V c k x ≤ n := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  exact mem_rankBound_iff_specializationRankCeiling (Over.mk p) x n

/-- Complete interiors have an exact test using the derived original local ceiling. -/
theorem originalCompleteInterior_iff_ceiling (n : ℕ) (o : Fin n)
    (x : normalizedFullRelationFrames f hL d V c k n o) :
    x ∈ completeInterior («p» := p) («q» := q) (Fin n) o ↔
      originalSpecializationRankCeiling f hL d V c k (first p q (Fin n) o x) ≤ n := by
  rw [completeInterior_eq_rankBound_preimage e]
  exact original_rankBound_iff_ceiling f hL d V c k _ n

/-- Every local original ceiling is bounded by the attained global original cutoff. -/
theorem originalSpecializationRank_le_cutoff (x : A.left) :
    originalSpecializationRankCeiling f hL d V c k x ≤ originalFrameRankCutoff f hL d V c k := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  apply specializationRankCeiling_minimal
  intro y n _ hy
  exact originalFrameRankCutoff_spec f hL d V c k y n hy

/-- At an exact original rank, equality with the local ceiling detects the entire finite locus. -/
theorem originalFiniteTarget_iff_rank_eq_ceiling (n : ℕ) (x : A.left)
    (hx : x ∈ exactRank (Over.mk p) n) :
    x ∈ finiteTargetOpen p ↔ originalSpecializationRankCeiling f hL d V c k x = n := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  change x ∈ finiteTargetOpen p ↔ specializationRankCeiling (Over.mk p) x = n
  rw [finiteTarget_iff_rankBound_of_exactRank e n x hx,
    mem_rankBound_iff_specializationRankCeiling]
  exact ⟨fun h ↦ Nat.le_antisymm h
    (specializationRankCeiling_spec (Over.mk p) x x n specializes_rfl hx.1),
    fun h ↦ h.le⟩

/-- Every residual original point has a strict rank gap and an exact-center nonextendible square. -/
theorem exists_original_residual_rankJump (x : A.left) (hx : x ∉ finiteTargetOpen p) :
    ∃ n : ℕ, x ∈ exactRank (Over.mk p) n ∧
      n < originalSpecializationRankCeiling f hL d V c k x ∧
      originalSpecializationRankCeiling f hL d V c k x ≤ originalFrameRankCutoff f hL d V c k ∧
      ∃ T : ValuativeCommSq (distinctScheme (Over.mk p) (Fin (n + 1))).hom,
        T.i₂ (closedPoint T.R) = x ∧ ¬ T.commSq.HasLift := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  obtain ⟨n, hn⟩ := exists_exactRank (Over.mk p) x
  have ho : x ∉ rankBoundOpen (Over.mk p) n :=
    fun h ↦ hx ((finiteTarget_iff_rankBound_of_exactRank e n x hn).mpr h)
  have hlt : n < originalSpecializationRankCeiling f hL d V c k x := by
    exact Nat.lt_of_not_ge fun h ↦ ho
      ((mem_rankBound_iff_specializationRankCeiling (Over.mk p) x n).mpr h)
  exact ⟨n, hn, hlt, originalSpecializationRank_le_cutoff f hL d V c k x,
    exists_rankJump_square_no_lift (Over.mk p) n x hn ho⟩

/-- Every original point is a specialization of a point with actual original boundary lifts. -/
theorem exists_original_lifting_generization
    (W : TopologicalSpace.Opens (Orbit eo)) (x : A.left) (hx : x ∈ (pullOpen eo W).val) :
    ∃ y : A.left, y ⤳ x ∧
      y ∈ rankStratumOpen (Over.mk p) (originalSpecializationRankCeiling f hL d V c k x) ∧
      ∃ O : TopologicalSpace.Opens (Orbit eo),
        O ≤ W ∧ projection eo y ∈ O ∧ Function.Surjective ((m).c.app (op O)) := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  obtain ⟨y, hyx, hy⟩ := specializationRankCeiling_attained (Over.mk p) x
  refine ⟨y, hyx, hy, ?_⟩
  exact exists_rankStratum_original_lifting_neighborhood f hL d V c k W _ y
    (hyx.mem_open (pullOpen eo W).val.isOpen hx) hy

end FLT.Mazur.HilbertChart.AffineRestriction
