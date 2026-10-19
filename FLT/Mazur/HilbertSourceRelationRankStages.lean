/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceConstructedOpenSections
public import FLT.Mazur.SchemeRelationNoetherianRestriction
public import FLT.Mazur.HilbertNormalizedUniformRank
public import FLT.Mazur.EquivalenceRelationBoundaryComponentRank
public import FLT.Mazur.RelativeRankResidualSectionDetection
public import FLT.Mazur.RelativeRankThickeningFinite

/-!
# Full original relation stages and solved matching-rank equations

Keep both independent endpoints and the unchanged frame size. Every relation
point has a rank between that size and the original cutoff. The matching
stages lie in the already constructed good open, so every invariant
coefficient satisfies their full equations at every infinitesimal order.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient
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
local notation "e" => fullRelationSchemeEquivalence f hL d V c k
attribute [local irreducible] relation AffineRestriction.fst AffineRestriction.snd
variable (n : ℕ) (o : Fin n)
local notation "N" => normalizedFullRelationFrames f hL d V c k n o
local notation "ρ" => normalizedOriginalBoundaryAction f hL d V c k n o
local notation "τ" => normalizedFullRelationAction f hL d V c k n o
local notation "j" => normalizedOriginalBoundaryInclusion f hL d V c k n o
local notation "b" => normalizedOriginalBoundaryEndpoint f hL d V c k n o
local notation "hj" => normalizedOriginalBoundaryAction_inclusion f hL d V c k n o
variable (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)
  (hU : ∀ σ : Equiv.Perm (Fin n),
    (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ U = U)

local notation "kS" => U.ι ≫ normalizedFullRelationFirst f hL d V c k n o
local notation "D" => SchemeRelationRestriction.doubleDomain p q kS
local notation "F" => SchemeRelationRestriction.fst p q kS
local notation "H" => SchemeRelationRestriction.snd p q kS

open RelativeOrderedTuples
local notation "endpoint" => F ≫ kS
local notation "cutoff" => originalFrameRankCutoff f hL d V c k
local notation "good" => originalSourceGoodRelationOpen f hL d V c k n o U hU
local instance relationStageOver_etale : Etale (Over.mk p).hom := inferInstanceAs (Etale p)
local instance relationStageOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)
local instance relationStageOver_compact : QuasiCompact (Over.mk p).hom :=
  inferInstanceAs (QuasiCompact p)

/-- The entire two-endpoint relation lies in the bounded original rank interval. -/
theorem originalSource_relation_rank_interval (x : D) :
    ∃ m : ℕ, n ≤ m ∧ m ≤ cutoff ∧ endpoint x ∈ exactRank (Over.mk p) m := by
  obtain ⟨m, hm⟩ := exists_exactRank (Over.mk p) (endpoint x)
  refine ⟨m, ?_, originalFrameRankCutoff_spec f hL d V c k _ m hm.1, hm⟩
  by_contra h
  have hn : endpoint x ∈ rankImageOpen (Over.mk p) n :=
    ⟨inclusion p q (Fin n) o (U.ι (F x)), rfl⟩
  exact hm.2 (rankImageOpen_antitone (Over.mk p) (Nat.lt_of_not_ge h) hn)

/-- Matching-rank relation points belong to the actual coefficient-independent good open. -/
theorem originalSource_relation_matching_good (x : D)
    (hx : endpoint x ∈ exactRank (Over.mk p) n) : x ∈ good := by
  apply originalSourceGoodRelationOpen_contains f hL d V c k n o U hU
  exact (chart_complete_iff_exactRank n o U (F x)).mpr hx

/-- Every invariant numerator already satisfies all full matching-stage equations. -/
theorem originalSource_relation_matching_equation
    (a : invariantCoordinates (restrictedAction τ U hU)) (order : ℕ) :
    (rankPullbackMap (Over.mk p) endpoint n order ≫ F).appTop a.val =
      (rankPullbackMap (Over.mk p) endpoint n order ≫ H).appTop a.val := by
  apply rankStage_eq_of_open (Over.mk p) endpoint n good
    (originalSource_relation_matching_good f hL d V c k n o U hU)
    ((F).appTop a.val) ((H).appTop a.val)
  exact originalSourceGoodRelationOpen_equalizes f hL d V c k n o U hU a

/-- Each residual relation stage has finite whole original source, without selecting branches. -/
theorem originalSource_relation_rankStage_finite (m order : ℕ) :
    IsFinite (pullback.snd p
      (rankPullbackMap (Over.mk p) endpoint m order ≫ endpoint)) := by
  let _ : LocallyQuasiFinite (Over.mk p).hom :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ (fst_finite_fiber f hL d V c k)
  exact finite_pullback_rankPullback (Over.mk p) endpoint m order

end FLT.Mazur.HilbertChart.AffineRestriction
