/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceConstructedOpenPrimeTests
public import FLT.Mazur.HilbertResidualRankCeiling
public import FLT.Mazur.HilbertCompleteInteriorCharts
public import FLT.Mazur.EquivalenceRelationExactRankInterior
public import FLT.Mazur.AffineHilbertDerivedNoetherianRelation

/-!
# Original source lifts on charts bounded by the local rank ceiling

A chartwise ceiling bound gives the unchanged scalar 1 as a safe denominator
at every original boundary prime. Such charts are constructed around every
complete frame whose endpoint lies in the actual finite target locus. Their
sizes may be strictly below the global original frame cutoff.
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
  normalizedFullRelationAction
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


open RelativeOrderedTuples SchemeOpenEnvelope
local instance localCeilingOver_etale : Etale (Over.mk p).hom := inferInstanceAs (Etale p)
local instance localCeilingOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)
local instance localCeilingOver_compact : QuasiCompact (Over.mk p).hom :=
  inferInstanceAs (QuasiCompact p)

/-- Local ceilings, rather than one global maximum, make every actual chart arrow good. -/
theorem originalSourceGoodRelationOpen_eq_top_of_localRankCeiling
    (hn : ∀ x ∈ U, originalSpecializationRankCeiling f hL d V c k (first p q (Fin n) o x) ≤ n) :
    Lgood = ⊤ := by
  apply top_le_iff.mp
  intro x _
  apply originalSourceGoodRelationOpen_contains f hL d V c k n o U hU
  apply completeInterior_subset
  apply (originalCompleteInterior_iff_ceiling f hL d V c k n o _).mpr
  exact hn _ (F x).property

/-- Scalar 1 avoids the whole bad relation locus under the actual local ceiling bound. -/
theorem originalSource_safe_of_localRankCeiling
    (hn : ∀ x ∈ U, originalSpecializationRankCeiling f hL d V c k (first p q (Fin n) o x) ≤ n)
    (P : PrimeSpectrum Ω) : P ∈ scalarNeighborhoodLocus σR Lgood := by
  apply (mem_scalarNeighborhoodLocus_iff σR Lgood P).mpr
  refine ⟨1, P.isPrime.one_notMem, ?_⟩
  rw [originalSourceGoodRelationOpen_eq_top_of_localRankCeiling f hL d V c k n o U hU hn]
  exact le_top

/-- All original localized coefficients lift on locally bounded charts, at any frame size. -/
theorem originalSource_all_surjective_of_localRankCeiling (ha : IsAffineOpen U)
    (hn : ∀ x ∈ U, originalSpecializationRankCeiling f hL d V c k (first p q (Fin n) o x) ≤ n)
    (P : Ideal Tsource) [P.IsPrime] :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
    Function.Surjective
      (originalSourceLocalizedCompatibleBoundaryMap f hL d V c k n o W U hU hUW P) :=
  originalSource_constructedOpen_surjective f hL d V c k n o W U hU hUW ha P
    (originalSource_safe_of_localRankCeiling f hL d V c k n o W U hU hUW hn _)

/-- Complete frames on the original finite locus construct charts with the local bound proved. -/
theorem exists_originalSource_localRankCeiling_chart
    (x : normalizedFullRelationFrames f hL d V c k n o)
    (hx : normalizedFullRelationFirst f hL d V c k n o x ∈ (pullOpen eo W).val)
    (hc : x ∈ completePointLocus («p» := p) («q» := q) (Fin n) o)
    (hf : first p q (Fin n) o x ∈ finiteTargetOpen p) :
    ∃ (U' : (normalizedFullRelationFrames f hL d V c k n o).Opens)
      (hU' : ∀ g : Equiv.Perm (Fin n), (τ g).hom ⁻¹ᵁ U' = U')
      (hUW' : U' ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ (pullOpen eo W).val),
      IsAffineOpen U' ∧ x ∈ U' ∧
      (∀ y ∈ U', originalSpecializationRankCeiling f hL d V c k (first p q (Fin n) o y) ≤ n) ∧
      ∀ P : PrimeSpectrum Tsource,
        let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U' hU' hUW'
        let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U' hU' hUW'
        Function.Surjective
          (originalSourceLocalizedCompatibleBoundaryMap f hL d V c k n o W U' hU' hUW'
            P.asIdeal) := by
  obtain ⟨U', hU', hUW', ha, hx', hC, _⟩ :=
    exists_completeInterior_orbit_chart f hL d V c k W n o x hx
      (complete_mem_interior_of_finiteTarget (Fin n) o x hc hf)
  have hb : ∀ y ∈ U',
      originalSpecializationRankCeiling f hL d V c k (first p q (Fin n) o y) ≤ n := by
    intro y hy
    exact (originalCompleteInterior_iff_ceiling f hL d V c k n o y).mp
      (le_completeInterior (Fin n) o U' hC hy)
  exact ⟨U', hU', hUW', ha, hx', hb, fun P ↦
    originalSource_all_surjective_of_localRankCeiling
      f hL d V c k n o W U' hU' hUW' ha hb P.asIdeal⟩

end FLT.Mazur.HilbertChart.AffineRestriction
