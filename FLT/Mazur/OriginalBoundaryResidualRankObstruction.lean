/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryRankCollision
public import FLT.Mazur.OriginalBoundaryResidualIdeal

/-!
# Principal rank neighborhoods on the original residual frontier

The sum with the existing residual ideal retains both bad image closures.
Its zero locus is exactly their intersection with the unequal-rank image
closure. A support bound by the whole V(Q) constructs actual common cores
on every required residual field test. The support bound is not assumed
as a record field and is not claimed to follow from scalar equality.
This controls neighborhoods; a collision-free fiber alone need not avoid
the closure of the collision image.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
open SchemeEffectiveEpiSections SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p]
local instance residualCollisionOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance residualCollisionOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance residualCollisionOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (J : A.IdealSheafData)
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "σ" => scalarMorphism (Subring.subtype R)
local notation "f" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "x" => pullback.fst f f ≫ J.subschemeι
local notation "y" => pullback.snd f f ≫ J.subschemeι
local notation "s" => pullback.fst f f ≫ f

/-- The rank obstruction restricted to the unchanged two-closure residual frontier. -/
def originalBoundaryResidualRankIdeal : Ideal R :=
  originalBoundaryRankCollisionIdeal (p := p) (q := q) J ⊔
    originalBoundaryResidualIdeal (p := p) (q := q) J

variable [IsAffine A]

omit [QuasiCompact p] in
/-- Both original bad closures remain present, without distributing closure over intersection. -/
theorem originalBoundaryResidualRankIdeal_zeroLocus :
    PrimeSpectrum.zeroLocus (originalBoundaryResidualRankIdeal (p := p) (q := q) J : Set R) =
      closure (s '' rankCollision (Over.mk p) x y) ∩
        (closure (σ '' (J.support : Set A)) ∩
          closure (σ '' (finiteTargetOpen p : Set A)ᶜ)) := by
  rw [originalBoundaryResidualRankIdeal, PrimeSpectrum.zeroLocus_sup,
    originalBoundaryRankCollisionIdeal, rankCollisionIdeal_zeroLocus,
    originalBoundaryResidualIdeal_zeroLocus]
  rfl

/-- A residual support bound yields a genuine original scalar excluding every rank collision. -/
theorem originalBoundary_residual_rank_denominator (Q : Ideal R)
    (hQ : PrimeSpectrum.zeroLocus
      (originalBoundaryResidualRankIdeal (p := p) (q := q) J : Set R) ⊆
        PrimeSpectrum.zeroLocus (Q : Set R))
    (P : PrimeSpectrum R)
    (hP : P ∈ closure (σ '' (J.support : Set A)) ∩
      closure (σ '' (finiteTargetOpen p : Set A)ᶜ))
    (hPQ : P ∉ PrimeSpectrum.zeroLocus (Q : Set R)) :
    ∃ r : R, r ∉ P.asIdeal ∧
      ∀ w : (pullback f f : Scheme), s w ∈ PrimeSpectrum.basicOpen r →
        ∃ n, x w ∈ exactRank (Over.mk p) n ∧ y w ∈ exactRank (Over.mk p) n := by
  apply (rankCollisionIdeal_not_le_iff (Over.mk p) x y s P).mp
  intro hbad
  apply hPQ
  apply hQ
  rw [originalBoundaryResidualRankIdeal_zeroLocus]
  refine ⟨?_, hP⟩
  rw [← rankCollisionIdeal_zeroLocus]
  exact hbad

omit [QuasiCompact p] [IsAffine A] in
/-- Explicit finite generation gives a uniform power in the sum of the two actual obstructions. -/
theorem exists_pow_le_originalBoundaryResidualRankIdeal (Q : Ideal R) (hfg : Q.FG)
    (hQ : PrimeSpectrum.zeroLocus
      (originalBoundaryResidualRankIdeal (p := p) (q := q) J : Set R) ⊆
        PrimeSpectrum.zeroLocus (Q : Set R)) :
    ∃ N : ℕ, Q ^ N ≤ originalBoundaryResidualRankIdeal (p := p) (q := q) J :=
  Ideal.exists_pow_le_of_le_radical_of_fg
    ((PrimeSpectrum.zeroLocus_subset_zeroLocus_iff _ _).mp hQ) hfg

variable [Etale q] [IsLocallyNoetherian A] [LocallyQuasiFinite p]
  (e : CategoryTheory.EquivalenceRelation p q)

/-- The residual support bound constructs common full boundary towers on actual field tests. -/
theorem originalBoundary_residual_common_core (Q : Ideal R)
    (hQ : PrimeSpectrum.zeroLocus
      (originalBoundaryResidualRankIdeal (p := p) (q := q) J : Set R) ⊆
        PrimeSpectrum.zeroLocus (Q : Set R))
    {K : Type} [Field K] (t : Spec (.of K) ⟶ pullback f f)
    (hP : s (t (IsLocalRing.closedPoint K)) ∈ closure (σ '' (J.support : Set A)) ∩
      closure (σ '' (finiteTargetOpen p : Set A)ᶜ))
    (hPQ : s (t (IsLocalRing.closedPoint K)) ∉ PrimeSpectrum.zeroLocus (Q : Set R)) :
    ∃ (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n),
      ∀ k, ∃ u v : Spec (.of K) ⟶ (rankStageCoreBoundaryIdeal e n a ha J k).subscheme,
        u ≫ rankStageCoreOriginalBoundaryMap e n a ha J k = t ≫ pullback.fst f f ∧
        v ≫ rankStageCoreOriginalBoundaryMap e n a ha J k = t ≫ pullback.snd f f := by
  obtain ⟨r, hrP, hr⟩ := originalBoundary_residual_rank_denominator J Q hQ
    (s (t (IsLocalRing.closedPoint K))) hP hPQ
  apply originalBoundary_common_core_of_rankCollisionIdeal J e t
  intro h
  exact hrP (h ((mem_rankCollisionIdeal_iff (Over.mk p) x y s r).mpr hr))

end FLT.Mazur.EquivalenceRelationOrderedFrames
