/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceBoundaryPrincipalCharts
public import FLT.Mazur.EquivalenceRelationBoundaryScalarCharts

/-!
# Genuine scalar matching charts for the original Hilbert source

All scalar primes remain primes of the original source-section ring. Scalar
neighborhoods are characterized by original component ranks, and their exact
closed obstruction records all limiting higher ranks over the scalar base.
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
local instance scalarOriginalChartNoetherian : IsNoetherian U.toScheme :=
  originalSource_affine_isNoetherian f hL d V c k n o U
    (show IsAffine U.toScheme from inferInstance)

open AffineScalarBoundaryNilpotence RelativeOrderedTuples
attribute [local irreducible] boundaryProduct boundaryCoordinate
local notation "tests" => originalSourceCompletenessTests f hL d V c k n o U hU
local notation "bdy" => chartBoundaryEndpoint n o U e hU σ κ
local notation "prod" => chartBoundaryProduct n o U e hU σ κ
local instance scalarOriginalOver_etale : Etale (Over.mk p).hom := inferInstanceAs (Etale p)
local instance scalarOriginalOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)

local notation "Cb" => Γ(boundaryProduct σ κ, ⊤)
local notation "rankOf" => boundaryPointRank n o U e hU σ κ
local notation "Itests" => boundaryTestIdeal σ κ tests

/-- The exact obstruction on the original scalar spectrum is the projected higher-rank closure. -/
theorem originalSource_scalarNilpotenceOpen_compl :
    (boundaryScalarNilpotenceOpen σ κ tests : Set (PrimeSpectrum Tsource))ᶜ =
      closure (boundaryScalarProjection σ κ ''
        {pointZ : boundaryProduct σ κ | n < rankOf pointZ}) :=
  boundaryScalarNilpotenceOpen_compl_eq_higher_image_closure n o U e hU σ κ

/-- Every excluded original scalar prime has a higher-rank original component generizing it. -/
theorem originalSource_scalar_obstruction_component (P : PrimeSpectrum Tsource)
    (hP : P ∉ boundaryScalarNilpotenceOpen σ κ tests) :
    ∃ Q : minimalPrimes Cb,
      (boundaryScalarProjection σ κ (boundaryComponentPoint σ κ Q)).asIdeal ≤ P.asIdeal ∧
        n < rankOf (boundaryComponentPoint σ κ Q) :=
  (not_mem_boundaryScalarNilpotenceOpen_iff_higher n o U e hU σ κ P).mp hP

attribute [local irreducible] boundaryPointRank boundaryComponentPoint boundaryTestIdeal
  boundaryPrincipalProjection boundaryPrincipalEndpoint boundaryScalarHom

/-- Covered original scalar primes have genuine scalar denominators killing a whole test power. -/
theorem originalSource_scalar_power_denominator (P : PrimeSpectrum Tsource)
    (hP : P ∈ boundaryScalarNilpotenceOpen σ κ tests) :
    ∃ (order : ℕ) (t : Tsource), t ∉ P.asIdeal ∧
      boundaryScalarHom σ κ t ∈ (Itests ^ order).annihilator :=
  (mem_boundaryScalarNilpotenceOpen σ κ tests P).mp hP

/-- A covered scalar prime has a faithful chart recovering a whole finite matching rank stage. -/
theorem originalSource_scalar_rank_chart (P : PrimeSpectrum Tsource)
    (hP : P ∈ boundaryScalarNilpotenceOpen σ κ tests) :
    ∃ t : Tsource, t ∉ P.asIdeal ∧ ∃ stage : ℕ,
      IsIso (rankPullbackMap (Over.mk p)
        (boundaryPrincipalEndpoint n o U e hU σ κ (boundaryScalarHom σ κ t)) n stage) := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  exact exists_boundary_scalar_rank_chart n o U e hU σ κ P hP

/-- At the original rank cutoff every original scalar prime has a matching neighborhood. -/
theorem originalSource_scalarNilpotenceOpen_eq_top_of_cutoff
    (hn : originalFrameRankCutoff f hL d V c k ≤ n) :
    boundaryScalarNilpotenceOpen σ κ tests = ⊤ := by
  apply (boundaryScalarNilpotenceOpen_eq_top_iff σ κ tests).mpr
  apply (boundaryNilpotenceOpen_eq_top_iff σ κ tests).mp
  exact originalSource_boundaryNilpotenceOpen_eq_top_of_cutoff f hL d V c k n o W U hU hUW hn

/-- At the derived cutoff each unchanged scalar prime receives an actual matching-stage chart. -/
theorem originalSource_scalar_rank_chart_of_cutoff
    (hn : originalFrameRankCutoff f hL d V c k ≤ n) (P : PrimeSpectrum Tsource) :
    ∃ t : Tsource, t ∉ P.asIdeal ∧ ∃ stage : ℕ,
      IsIso (rankPullbackMap (Over.mk p)
        (boundaryPrincipalEndpoint n o U e hU σ κ (boundaryScalarHom σ κ t)) n stage) := by
  apply originalSource_scalar_rank_chart f hL d V c k n o W U hU hUW P
  rw [originalSource_scalarNilpotenceOpen_eq_top_of_cutoff f hL d V c k n o W U hU hUW hn]
  trivial

end FLT.Mazur.HilbertChart.AffineRestriction
