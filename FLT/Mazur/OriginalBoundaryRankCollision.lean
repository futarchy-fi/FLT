/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryFieldArrowRank
public import FLT.Mazur.OriginalBoundaryComparisonNeighborhood
public import FLT.Mazur.RelativeRankCollisionIdeal

/-!
# A rank obstruction on the unchanged original scalar kernel pair

The ideal lives in the original invariant ring. Every actual comparison point
avoids the collision set. Principal exclusion of this set proves equal exact
rank for all field tests and constructs full boundary factors at every order.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p]
local instance collisionOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance collisionOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance collisionOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (J : A.IdealSheafData)
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "x" => pullback.fst f f ≫ J.subschemeι
local notation "y" => pullback.snd f f ≫ J.subschemeι
local notation "s" => pullback.fst f f ≫ f

/-- Original invariant scalars that exclude unequal-rank pairs on their entire principal locus. -/
def originalBoundaryRankCollisionIdeal : Ideal R := rankCollisionIdeal (Over.mk p) x y s

variable (e : CategoryTheory.EquivalenceRelation p q) (hJ : J.comap p = J.comap q)

include e in
/-- An actual full comparison point cannot have unequal original endpoint ranks. -/
theorem originalBoundary_comparison_not_rankCollision
    (w : (pullback f f : Scheme))
    (hw : w ∈ Set.range (originalBoundaryComparison p q J hJ)) :
    w ∉ rankCollision (Over.mk p) x y := by
  obtain ⟨d, rfl⟩ := hw
  apply (not_mem_rankCollision_iff (Over.mk p) x y _).mpr
  obtain ⟨n, hn⟩ := exists_exactRank (Over.mk p) (p (pullback.fst p J.subschemeι d))
  have hx : originalBoundaryComparison p q J hJ ≫ x = pullback.fst p J.subschemeι ≫ p := by
    simp only [originalBoundaryComparison, pullback.lift_fst_assoc, pullback.condition]
  have hy : originalBoundaryComparison p q J hJ ≫ y = pullback.fst p J.subschemeι ≫ q := by
    simp only [originalBoundaryComparison, pullback.lift_snd_assoc, InvariantIdealRelation.snd_ι]
  refine ⟨n, ?_, ?_⟩
  · exact (congrArg (fun g ↦ g d) hx) ▸ hn
  · exact (congrArg (fun g ↦ g d) hy) ▸
      ((exactRank_endpoint_iff e n (pullback.fst p J.subschemeι d)).mp hn)

include e in
/-- Principal full comparison coverage necessarily excludes the constructed rank obstruction. -/
theorem originalBoundaryRankCollisionIdeal_of_principal_coverage (r : R)
    (hr : ∀ w : (pullback f f : Scheme), s w ∈ PrimeSpectrum.basicOpen r →
      w ∈ Set.range (originalBoundaryComparison p q J hJ)) :
    r ∈ originalBoundaryRankCollisionIdeal (p := p) (q := q) J := by
  apply (mem_rankCollisionIdeal_iff (Over.mk p) x y s r).mpr
  intro w hw
  exact (not_mem_rankCollision_iff (Over.mk p) x y w).mp
    (originalBoundary_comparison_not_rankCollision J e hJ w (hr w hw))

variable [Etale q] [IsLocallyNoetherian A] [IsAffine A] [LocallyQuasiFinite p]

/-- Nonvanishing of an actual original obstruction scalar constructs both full endpoint towers. -/
theorem originalBoundary_common_core_of_rankCollisionIdeal {K : Type} [Field K]
    (t : Spec (.of K) ⟶ pullback f f)
    (h : ¬ originalBoundaryRankCollisionIdeal (p := p) (q := q) J ≤
      (s (t (IsLocalRing.closedPoint K))).asIdeal) :
    ∃ (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n),
      ∀ k, ∃ u v : Spec (.of K) ⟶ (rankStageCoreBoundaryIdeal e n a ha J k).subscheme,
        u ≫ rankStageCoreOriginalBoundaryMap e n a ha J k = t ≫ pullback.fst f f ∧
        v ≫ rankStageCoreOriginalBoundaryMap e n a ha J k = t ≫ pullback.snd f f := by
  obtain ⟨n, hx, hy⟩ := same_rank_of_rankCollisionIdeal_not_le (Over.mk p) x y s
    (t (IsLocalRing.closedPoint K)) h
  obtain ⟨a, ha, hc⟩ := exists_rankStage_field_boundary_pair e J n
    (t ≫ pullback.fst f f) (t ≫ pullback.snd f f) hx hy
  exact ⟨n, a, ha, hc⟩

end FLT.Mazur.EquivalenceRelationOrderedFrames
