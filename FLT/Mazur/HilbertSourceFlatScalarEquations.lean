/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceTestKernelObstruction
public import FLT.Mazur.AffineBoundaryFppfScalarTests
public import FLT.Mazur.ScalarNilpotenceMinimalFiber
public import FLT.Mazur.SchemeFiniteGroupQuotientFiniteType

/-!
# Actual flat scalar branches for original Hilbert rank exclusion

Power equations on the full Cartesian coefficient pullback may use branch
functions. Flat descent constructs an original scalar denominator and recovers
the unchanged matching rank. The independent geometric branch equations remain
to be constructed on required residual primes.
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
local instance flatEquationChartNoetherian : IsNoetherian U.toScheme :=
  originalSource_affine_isNoetherian f hL d V c k n o U
    (show IsAffine U.toScheme from inferInstance)

open AffineScalarBoundaryNilpotence RelativeOrderedTuples
attribute [local irreducible] boundaryProduct boundaryCoordinate
local notation "tests" => originalSourceCompletenessTests f hL d V c k n o U hU
local notation "bdy" => chartBoundaryEndpoint n o U e hU σ κ
local notation "prod" => chartBoundaryProduct n o U e hU σ κ
local instance flatEquationOver_etale : Etale (Over.mk p).hom := inferInstanceAs (Etale p)
local instance flatEquationOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)

local notation "Cb" => Γ(boundaryProduct σ κ, ⊤)
local notation "rankOf" => boundaryPointRank n o U e hU σ κ
local notation "Itests" => boundaryTestIdeal σ κ tests

local instance flatEquationProjection_quasiFinite : LocallyQuasiFinite p :=
  LocallyQuasiFinite.of_finite_preimage_singleton _ (fst_finite_fiber f hL d V c k)

local notation "ceiling" => originalSourceScalarRankCeiling f hL d V c k n o W U hU hUW
local notation "higher" => boundaryRankOpen n o U e hU σ κ (n + 1)
local notation "φ" => boundaryHigherScalarMap n o U e hU σ κ

/-- Branch functions suffice: they need not be images of original Hilbert source scalars. -/
theorem originalSource_ceiling_eq_of_flat_scalar_equations 
    {Y : Scheme} (g : Y ⟶ Spec (.of Tsource)) [Flat g]
    [LocallyOfFinitePresentation g] (y : Y) (x : Γ(Y, ⊤))
    (hx : y ∈ Y.basicOpen x)
    (he : ∀ t ∈ tests, ∃ order : ℕ,
      ((pullback.fst (boundaryScalarProjection σ κ) g).appTop
        (boundaryCoordinate σ κ t)) ^ order *
        (pullback.snd (boundaryScalarProjection σ κ) g).appTop x = 0) :
    ceiling (g y) = n := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  apply (mem_boundaryScalarNilpotenceOpen_iff_ceiling n o U e hU σ κ (g y)).mp
  exact boundaryScalar_mem_of_flat_equations σ κ tests g y x hx he

/-- Flat branch equations produce a whole original scalar rank chart, preserving n. -/
theorem originalSource_rank_chart_of_flat_scalar_equations 
    {Y : Scheme} (g : Y ⟶ Spec (.of Tsource)) [Flat g]
    [LocallyOfFinitePresentation g] (y : Y) (x : Γ(Y, ⊤))
    (hx : y ∈ Y.basicOpen x)
    (he : ∀ t ∈ tests, ∃ order : ℕ,
      ((pullback.fst (boundaryScalarProjection σ κ) g).appTop
        (boundaryCoordinate σ κ t)) ^ order *
        (pullback.snd (boundaryScalarProjection σ κ) g).appTop x = 0) :
    ∃ t : Tsource, t ∉ (g y).asIdeal ∧ ∃ stage : ℕ,
      IsIso (rankPullbackMap (Over.mk p)
        (boundaryPrincipalEndpoint n o U e hU σ κ (boundaryScalarHom σ κ t)) n stage) := by
  apply originalSource_scalar_rank_chart f hL d V c k n o W U hU hUW (g y)
  exact boundaryScalar_mem_of_flat_equations σ κ tests g y x hx he

/-- The returned power equation lives in the unchanged full Hilbert boundary product. -/
theorem originalSource_denominator_of_flat_scalar_equations 
    {Y : Scheme} (g : Y ⟶ Spec (.of Tsource)) [Flat g]
    [LocallyOfFinitePresentation g] (y : Y) (x : Γ(Y, ⊤))
    (hx : y ∈ Y.basicOpen x)
    (he : ∀ t ∈ tests, ∃ order : ℕ,
      ((pullback.fst (boundaryScalarProjection σ κ) g).appTop
        (boundaryCoordinate σ κ t)) ^ order *
        (pullback.snd (boundaryScalarProjection σ κ) g).appTop x = 0) :
    ∃ (order : ℕ) (scalar : Tsource), scalar ∉ (g y).asIdeal ∧
      boundaryScalarHom σ κ scalar ∈ (Itests ^ order).annihilator :=
  boundaryScalar_denominator_of_flat_equations σ κ tests g y x hx he

/-- Each completeness test may use a different branch and a different branch scalar. -/
theorem originalSource_ceiling_eq_of_independent_flat_tests
    (Ys : tests → Scheme) (gs : ∀ t, Ys t ⟶ Spec (.of Tsource))
    [∀ t, Flat (gs t)] [∀ t, LocallyOfFinitePresentation (gs t)]
    (P : PrimeSpectrum Tsource) (ys : ∀ t, Ys t) (hy : ∀ t, gs t (ys t) = P)
    (xs : ∀ t, Γ(Ys t, ⊤)) (hx : ∀ t, ys t ∈ (Ys t).basicOpen (xs t))
    (he : ∀ t, ∃ order : ℕ,
      ((pullback.fst (boundaryScalarProjection σ κ) (gs t)).appTop
        (boundaryCoordinate σ κ t.val)) ^ order *
        (pullback.snd (boundaryScalarProjection σ κ) (gs t)).appTop (xs t) = 0) :
    ceiling P = n := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  apply (mem_boundaryScalarNilpotenceOpen_iff_ceiling n o U e hU σ κ P).mp
  exact boundaryScalar_mem_of_independent_flat_tests σ κ tests Ys gs P ys hy xs hx he

/-- Exact matching suffices at original minimal scalar centers, retaining all nilpotents. -/
theorem originalSource_ceiling_eq_of_minimal_matching_fiber
    (P : PrimeSpectrum Tsource) (hP : P.asIdeal ∈ minimalPrimes Tsource)
    (hf : ∀ pointZ : boundaryProduct σ κ,
      boundaryScalarProjection σ κ pointZ = P → rankOf pointZ = n) : ceiling P = n := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  apply (mem_boundaryScalarNilpotenceOpen_iff_ceiling n o U e hU σ κ P).mp
  apply boundaryScalar_mem_of_minimal_fiber σ κ tests P hP
  intro pointZ hz
  apply (boundaryTestIdeal_le_point_iff σ κ tests pointZ).mp
  exact (boundaryTestIdeal_le_iff_matching_rank n o U e hU σ κ pointZ).mpr (hf pointZ hz)

/-- An actual fppf cover of the original scalar base supplies its own lifting points. -/
theorem originalSource_ceiling_eq_of_fppf_scalar_tests
    (C : Scheme.Cover.{0} Scheme.fppfPrecoverage (Spec (.of Tsource)))
    (P : PrimeSpectrum Tsource)
    (h : ∀ idx, ∀ y : C.X idx, C.f idx y = P → ∀ t ∈ tests,
      ∃ (x : Γ(C.X idx, ⊤)) (order : ℕ), y ∈ (C.X idx).basicOpen x ∧
        ((pullback.fst (boundaryScalarProjection σ κ) (C.f idx)).appTop
          (boundaryCoordinate σ κ t)) ^ order *
          (pullback.snd (boundaryScalarProjection σ κ) (C.f idx)).appTop x = 0) :
    ceiling P = n := by
  let _ := selectedAffineHilbertSource_isNoetherian f d V k
  apply (mem_boundaryScalarNilpotenceOpen_iff_ceiling n o U e hU σ κ P).mp
  exact boundaryScalar_mem_of_fppf_scalar_tests σ κ tests C P h

end FLT.Mazur.HilbertChart.AffineRestriction
