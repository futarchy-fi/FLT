/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceBoundaryRankStages
public import FLT.Mazur.EquivalenceRelationBoundaryTestCharts
public import FLT.Mazur.AffineBoundaryTestFactorization

/-!
# Original Hilbert boundary test neighborhoods and finite rank obstructions

The original fixed tests construct ideal-power neighborhoods with exact-rank
chart lifts. Every compact matching-rank coefficient chart factors through a
finite order. Full-product nilpotence is detected by the bounded higher ranks;
their unconditional absence on the required residual charts remains open.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open RelativeRelationOrbit InvariantOpenRelationDiagram
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
local notation "eo" => equivalence f hL d V c k
local notation "ec" => originalClosedEquivalence f hL d V c k
local notation "i" => Over.Hom.left (originalBoundarySourceMap f hL d V c k)
local notation "r" => Over.Hom.left (originalClosedFst f hL d V c k)
local notation "s" => Over.Hom.left (originalClosedSnd f hL d V c k)
local notation "z" => Over.Hom.left (originalClosedArrow f hL d V c k)
local notation "hr" => originalClosedFst_isPullback f hL d V c k
local notation "hs" => congrArg Over.Hom.left (originalClosedArrow_snd f hL d V c k)
local notation "m" => originalClosedInvariantMap f hL d V c k
attribute [local irreducible] originalBoundarySource originalBoundarySourceMap
  originalClosedRelation originalClosedFst originalClosedSnd originalClosedArrow
  originalClosedEquivalence relation AffineRestriction.fst AffineRestriction.snd equivalence
variable (n : ℕ) (o : Fin n)
local notation "N" => normalizedFullRelationFrames f hL d V c k n o
local notation "ρ" => normalizedOriginalBoundaryAction f hL d V c k n o
local notation "τ" => normalizedFullRelationAction f hL d V c k n o
local notation "j" => normalizedOriginalBoundaryInclusion f hL d V c k n o
local notation "b" => normalizedOriginalBoundaryEndpoint f hL d V c k n o
local notation "hj" => normalizedOriginalBoundaryAction_inclusion f hL d V c k n o
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
local notation "Uc" => (pullOpen ec Wc).val
variable (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)
  (hU : ∀ σ : Equiv.Perm (Fin n),
    (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ U = U)
  (hUW : U ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ
    (pullOpen (equivalence f hL d V c k) W).val)

local notation "Ω" => (invariantSheaf eo).obj.obj (op W)
local notation "Sinv" => invariantCoordinates (restrictedAction τ U hU)
local notation "E" => (pullOpen eo W).val

local notation "kS" => U.ι ≫ normalizedFullRelationFirst f hL d V c k n o
local notation "D" => SchemeRelationRestriction.doubleDomain p q kS
local notation "F" => SchemeRelationRestriction.fst p q kS
local notation "H" => SchemeRelationRestriction.snd p q kS
local notation "τU" => restrictedAction τ U hU
local notation "jU" => j ∣_ U
local notation "σ" => normalizedOriginalScalarMap f hL d V c k n o W U hU hUW
local notation "σ₀" => invariantScalarCoordinates τU σ
local notation "Tsource" => (sourceSheaf ec).obj.obj (op Wc)
local notation "κ" => ((invariantInclusion ec).hom.app (op Wc)).hom.comp
  (originalClosedSectionPullback f hL d V c k W)

attribute [local irreducible] normalizedOriginalScalarMap
  SchemeRelationRestriction.doubleDomain SchemeRelationRestriction.fst
  SchemeRelationRestriction.snd SchemeRelationRestriction.arrow

local notation "Bsource" => invariantCoordinates (boundaryOpenAction ρ τ j hj U hU)
local notation "α" => normalizedOriginalBoundaryHom f hL d V c k n o W U hU hUW

attribute [local irreducible] normalizedOriginalBoundary
  normalizedOriginalBoundaryInclusion normalizedOriginalBoundaryAction
  originalSourceCompatibleModule

local notation "Csource" => originalSourceCompatibleModule f hL d V c k n o W U hU hUW
local notation "βsource" => originalSourceCompatibleBoundaryMap f hL d V c k n o W U hU hUW

attribute [local irreducible] OriginalPrimeIntegralFiber.localizedMap
  invariantSheaf sourceSheaf invariantInclusion originalClosedSectionPullback
  invariantScalarCoordinates

open SchemeScalarPrincipalNeighborhood
local notation "Lgood" => originalSourceGoodRelationOpen f hL d V c k n o U hU
local notation "Ogood" => originalSourceConstructedOpen f hL d V c k n o U hU
local notation "σR" => (F).appTop.hom.comp σ₀


variable [IsAffine U.toScheme]
local instance testNeighborhoodCompletenessNoetherian :
    TopologicalSpace.NoetherianSpace U.toScheme := by
  let _ := originalSource_affine_isNoetherian f hL d V c k n o U
    (show IsAffine U.toScheme from inferInstance)
  infer_instance

open AffineScalarBoundaryNilpotence
attribute [local irreducible] boundaryProduct boundaryCoordinate
local notation "tests" => originalSourceCompletenessTests f hL d V c k n o U hU
local notation "C" => U.ι ⁻¹' completePointLocus («p» := p) («q» := q) (Fin n) o

local notation "Cb" => Γ(boundaryProduct σ κ, ⊤)
open RelativeOrderedTuples
local instance testNeighborhoodHilbertOver_etale : Etale (Over.mk p).hom :=
  inferInstanceAs (Etale p)
local instance testNeighborhoodHilbertOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)

local instance testNeighborhoodHilbertOver_compact : QuasiCompact (Over.mk p).hom :=
  inferInstanceAs (QuasiCompact p)
local notation "bdy" => chartBoundaryEndpoint n o U e hU σ κ

/-- Only the finitely many higher rank values up to the original cutoff need exclusion. -/
theorem originalSource_boundary_nilpotent_iff_bounded_higher_empty (powK : ℕ) :
    IsNilpotent (boundaryTestIdeal σ κ tests) ↔
      ∀ rankM : ℕ, n < rankM → rankM ≤ originalFrameRankCutoff f hL d V c k →
        IsEmpty (rankPullbackThickening (Over.mk p) bdy rankM powK) := by
  refine (boundaryTestIdeal_nilpotent_iff_higher_empty n o U e hU σ κ powK).trans ?_
  constructor
  · exact fun h rankM hm _ ↦ h rankM hm
  · intro h rankM hm
    by_cases hb : rankM ≤ originalFrameRankCutoff f hL d V c k
    · exact h rankM hm hb
    · refine ⟨fun y ↦ ?_⟩
      have hRank := rankPullback_endpoint (Over.mk p) bdy rankM powK y
      exact hb (originalFrameRankCutoff_spec f hL d V c k _ rankM hRank.1)

/-- The constructed original test neighborhood has exact rank on every actual chart lift. -/
theorem originalSource_testChart_exactRank (powK : ℕ)
    (y : boundaryTestChart n o U e hU σ κ powK) :
    boundaryTestChartEndpoint n o U e hU σ κ powK y ∈ exactRank (Over.mk p) n :=
  boundaryTestChartEndpoint_exactRank n o U e hU σ κ powK y

/-- Higher ranks are unconditionally excluded over all constructed test-ideal orders. -/
theorem originalSource_testChart_higher_empty (powK rankM order : ℕ) (hm : n < rankM) :
    IsEmpty (rankPullbackThickening (Over.mk p)
      (boundaryTestChartEndpoint n o U e hU σ κ powK) rankM order) :=
  boundaryTestChart_higher_empty n o U e hU σ κ powK rankM order hm

/-- Matching rank charts factor through a finite original test order as scheme morphisms. -/
theorem originalSource_matching_stage_factors (powK : ℕ)
    {Y : Scheme.{0}} [CompactSpace Y]
    (v : Y ⟶ rankPullbackThickening (Over.mk p) bdy n powK) :
    ∃ (order : ℕ) (w : Y ⟶ boundaryTestThickening σ κ tests order),
      w ≫ boundaryTestThickeningMap σ κ tests order =
        v ≫ boundaryRankProductMap n o U e hU σ κ powK n :=
  exists_boundaryTestThickening_factor σ κ tests _
    (originalSource_matching_rankStage_testIdeal_nilpotent f hL d V c k n o W U hU hUW powK v)

/-- A failed minimal-component equation has a bounded higher-stage witness at that same point. -/
theorem originalSource_component_failure_higher_stage (powK : ℕ)
    (t : Sinv) (ht : t ∈ tests) (Q : minimalPrimes Cb)
    (hQ : Ideal.Quotient.mk Q.val (boundaryCoordinate σ κ t) ≠ 0) :
    ∃ (rankM : ℕ) (y : rankPullbackThickening (Over.mk p) bdy rankM powK),
      n < rankM ∧ rankM ≤ originalFrameRankCutoff f hL d V c k ∧
      boundaryRankProductMap n o U e hU σ κ powK rankM y =
        boundaryComponentPoint σ κ Q := by
  obtain ⟨rankM, y, hn, hb, hy⟩ := exists_originalSource_boundary_rank_stage
    f hL d V c k n o W U hU hUW powK (boundaryComponentPoint σ κ Q)
  refine ⟨rankM, y, lt_of_le_of_ne hn ?_, hb, hy⟩
  intro he
  subst rankM
  have hc := boundaryRank_matching_complete n o U e hU σ κ powK y
  rw [hy] at hc
  exact hQ ((boundaryComponent_equation_iff σ κ Q t).mpr
    ((mem_closedOrbitImage_iff_tests τU C (completeChart_isClosed (Fin n) o U) _).mp hc t ht))

end FLT.Mazur.HilbertChart.AffineRestriction
