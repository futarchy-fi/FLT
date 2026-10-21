/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryGenerizingRanks
public import FLT.Mazur.RelativeRankCollisionFiniteLifts

/-!
# Full-source nonfiniteness at original boundary collision witnesses

An actual original rank obstruction constructs a valuation square. Every
lift whose closed pair lies in the original comparison image has a nonfinite
full endpoint pullback. Conversely, finite endpoint lifts through that actual
image construct an original principal rank neighborhood. Existence and
finiteness of such lifts remain geometric obligations, not record fields.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
open SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [IsAffine A] [IsLocallyNoetherian A]
local instance finiteValuationOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance finiteValuationOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance finiteValuationOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
local instance finiteValuationBase_noetherian : IsNoetherian A := ⟨⟩
variable (J : A.IdealSheafData)
local instance finiteValuationBoundary_affine : IsAffine J.subscheme :=
  isAffine_of_isAffineHom J.subschemeι
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "σ" => scalarMorphism (Subring.subtype R)
local notation "f" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "x" => pullback.fst f f ≫ J.subschemeι
local notation "y" => pullback.snd f f ≫ J.subschemeι
local notation "s" => pullback.fst f f ≫ f
variable (e : CategoryTheory.EquivalenceRelation p q) (hJ : J.comap p = J.comap q)

include e in
/-- Every actual scalar rank obstruction has a witness forcing full endpoint nonfiniteness. -/
theorem originalBoundary_collision_valuation_not_finite (P : PrimeSpectrum R)
    (hP : originalBoundaryRankCollisionIdeal (p := p) (q := q) J ≤ P.asIdeal) :
    ∃ V : ValuativeCommSq s, V.i₂ (closedPoint V.R) = P ∧
      V.i₁ default ∈ rankCollision (Over.mk p) x y ∧
      ∀ l : V.commSq.LiftStruct,
        l.l (closedPoint V.R) ∈ Set.range (originalBoundaryComparison p q J hJ) →
        ¬ IsFinite (pullback.snd p (l.l ≫ x)) ∨
          ¬ IsFinite (pullback.snd p (l.l ≫ y)) := by
  rw [originalBoundaryRankCollisionIdeal, rankCollisionIdeal_le_iff_valuation] at hP
  obtain ⟨V, hV, hVP⟩ := hP
  refine ⟨V, hVP, hV, fun l hl ↦ ?_⟩
  exact rankCollision_lift_not_finite (Over.mk p) x y s V l hV
    (originalBoundary_comparison_not_rankCollision J e hJ _ hl)

include e in
/-- Actual comparison lifts with full finite endpoint sources exclude the original obstruction. -/
theorem originalBoundary_rank_exclusion_of_finite_lifts (P : PrimeSpectrum R)
    (h : ∀ V : ValuativeCommSq s, V.i₂ (closedPoint V.R) = P →
      ∃ l : V.commSq.LiftStruct,
        l.l (closedPoint V.R) ∈ Set.range (originalBoundaryComparison p q J hJ) ∧
        IsFinite (pullback.snd p (l.l ≫ x)) ∧ IsFinite (pullback.snd p (l.l ≫ y))) :
    ¬ originalBoundaryRankCollisionIdeal (p := p) (q := q) J ≤ P.asIdeal := by
  intro hP
  obtain ⟨V, hVP, _, hbad⟩ := originalBoundary_collision_valuation_not_finite J e hJ P hP
  obtain ⟨l, hl, hx, hy⟩ := h V hVP
  exact (hbad l hl).elim (fun hn ↦ hn hx) (fun hn ↦ hn hy)

include e in
/-- Full finite lifted geometry yields one scalar neighborhood for every original boundary pair. -/
theorem originalBoundary_rank_denominator_of_finite_lifts (P : PrimeSpectrum R)
    (h : ∀ V : ValuativeCommSq s, V.i₂ (closedPoint V.R) = P →
      ∃ l : V.commSq.LiftStruct,
        l.l (closedPoint V.R) ∈ Set.range (originalBoundaryComparison p q J hJ) ∧
        IsFinite (pullback.snd p (l.l ≫ x)) ∧ IsFinite (pullback.snd p (l.l ≫ y))) :
    ∃ r : R, r ∉ P.asIdeal ∧
      ∀ w : (pullback f f : Scheme), s w ∈ PrimeSpectrum.basicOpen r →
        ∃ n, x w ∈ exactRank (Over.mk p) n ∧ y w ∈ exactRank (Over.mk p) n :=
  (rankCollisionIdeal_not_le_iff (Over.mk p) x y s P).mp
    (originalBoundary_rank_exclusion_of_finite_lifts J e hJ P h)

include e in
/-- The finite-lift construction suffices on precisely the unchanged original residual frontier. -/
theorem originalBoundary_residual_rank_support_of_finite_lifts (Q : Ideal R)
    (h : ∀ P : PrimeSpectrum R,
      P ∈ closure (σ '' (J.support : Set A)) ∩
        closure (σ '' (finiteTargetOpen p : Set A)ᶜ) →
      P ∉ PrimeSpectrum.zeroLocus (Q : Set R) →
      ∀ V : ValuativeCommSq s, V.i₂ (closedPoint V.R) = P →
      ∃ l : V.commSq.LiftStruct,
        l.l (closedPoint V.R) ∈ Set.range (originalBoundaryComparison p q J hJ) ∧
        IsFinite (pullback.snd p (l.l ≫ x)) ∧ IsFinite (pullback.snd p (l.l ≫ y))) :
    PrimeSpectrum.zeroLocus
      (originalBoundaryResidualRankIdeal (p := p) (q := q) J : Set R) ⊆
        PrimeSpectrum.zeroLocus (Q : Set R) := by
  apply (originalBoundary_residual_rank_support_iff J Q).mpr
  intro P hP hPQ
  exact (originalBoundary_rank_neighborhood_iff J P).mp
    (originalBoundary_rank_exclusion_of_finite_lifts J e hJ P (h P hP hPQ))

end FLT.Mazur.EquivalenceRelationOrderedFrames
