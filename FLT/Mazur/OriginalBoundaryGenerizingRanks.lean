/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryResidualRankObstruction
public import FLT.Mazur.RelativeRankCollisionGenerizations

/-!
# Actual generizing collisions on the original residual frontier

The original affine kernel pair is qcqs even when its coordinate ring is
not Noetherian. Constructible compactness therefore computes the collision
image closure using actual original pairs above generizing scalar primes.
Both original bad closures and the whole V(Q) remain in the residual test.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
open SchemeEffectiveEpiSections SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [IsAffine A] [IsLocallyNoetherian A]
local instance generizingOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance generizingOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance generizingOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
local instance generizingBase_noetherian : IsNoetherian A := ⟨⟩
variable (J : A.IdealSheafData)
local instance generizingBoundary_affine : IsAffine J.subscheme :=
  isAffine_of_isAffineHom J.subschemeι
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "σ" => scalarMorphism (Subring.subtype R)
local notation "f" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "x" => pullback.fst f f ≫ J.subschemeι
local notation "y" => pullback.snd f f ≫ J.subschemeι
local notation "s" => pullback.fst f f ≫ f

/-- Failure has an actual unequal-rank pair with an original scalar prime generizing the center. -/
theorem originalBoundary_rank_obstruction_iff (P : PrimeSpectrum R) :
    originalBoundaryRankCollisionIdeal (p := p) (q := q) J ≤ P.asIdeal ↔
      ∃ w : (pullback f f : Scheme),
        (s w).asIdeal ≤ P.asIdeal ∧
        ∃ n m : ℕ, n ≠ m ∧ x w ∈ exactRank (Over.mk p) n ∧
          y w ∈ exactRank (Over.mk p) m := by
  rw [originalBoundaryRankCollisionIdeal,
    rankCollisionIdeal_le_iff_generizing_collision]
  exact exists_congr fun _ ↦ and_comm

/-- The unchanged original rank obstruction is excluded by exactly the full generizing test. -/
theorem originalBoundary_rank_neighborhood_iff (P : PrimeSpectrum R) :
    ¬ originalBoundaryRankCollisionIdeal (p := p) (q := q) J ≤ P.asIdeal ↔
      ∀ w : (pullback f f : Scheme), (s w).asIdeal ≤ P.asIdeal →
        ∃ n, x w ∈ exactRank (Over.mk p) n ∧ y w ∈ exactRank (Over.mk p) n :=
  rankCollisionIdeal_not_le_iff_generizing_ranks (Over.mk p) x y s P

/-- No closed-image hypothesis is needed to construct the original principal rank neighborhood. -/
theorem originalBoundary_rank_denominator_of_generizations (P : PrimeSpectrum R)
    (h : ∀ w : (pullback f f : Scheme), (s w).asIdeal ≤ P.asIdeal →
      ∃ n, x w ∈ exactRank (Over.mk p) n ∧ y w ∈ exactRank (Over.mk p) n) :
    ∃ r : R, r ∉ P.asIdeal ∧
      ∀ w : (pullback f f : Scheme), s w ∈ PrimeSpectrum.basicOpen r →
        ∃ n, x w ∈ exactRank (Over.mk p) n ∧ y w ∈ exactRank (Over.mk p) n :=
  exists_same_rank_principal_of_generizing_ranks (Over.mk p) x y s P h

/-- The full residual support bound is equivalent to actual generizing rank agreement. -/
theorem originalBoundary_residual_rank_support_iff (Q : Ideal R) :
    (PrimeSpectrum.zeroLocus
      (originalBoundaryResidualRankIdeal (p := p) (q := q) J : Set R) ⊆
        PrimeSpectrum.zeroLocus (Q : Set R)) ↔
    ∀ P : PrimeSpectrum R,
      P ∈ closure (σ '' (J.support : Set A)) ∩
        closure (σ '' (finiteTargetOpen p : Set A)ᶜ) →
      P ∉ PrimeSpectrum.zeroLocus (Q : Set R) →
      ∀ w : (pullback f f : Scheme), (s w).asIdeal ≤ P.asIdeal →
        ∃ n, x w ∈ exactRank (Over.mk p) n ∧ y w ∈ exactRank (Over.mk p) n := by
  rw [originalBoundaryResidualRankIdeal_zeroLocus]
  constructor
  · intro h P hP hPQ
    apply (originalBoundary_rank_neighborhood_iff J P).mp
    intro hbad
    apply hPQ (h ⟨?_, hP⟩)
    rw [← rankCollisionIdeal_zeroLocus]
    exact hbad
  · intro h P hP
    by_contra hPQ
    have hr := (originalBoundary_rank_neighborhood_iff J P).mpr (h P hP.2 hPQ)
    apply hr
    have hc := hP.1
    rw [← rankCollisionIdeal_zeroLocus] at hc
    exact hc

end FLT.Mazur.EquivalenceRelationOrderedFrames
