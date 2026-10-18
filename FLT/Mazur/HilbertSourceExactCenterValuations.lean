/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceOriginalDomainComponents
public import FLT.Mazur.SchemeBadAffineCoverExactValuations

/-!
# Exact original-center poles on the unchanged Hilbert charts

Failure of original local integrality constructs an actual chart square with
an original generator pole at the exact contracted prime. Conversely, regularity
there recovers original equations and lifts on a common principal neighborhood.
Whole original scalar-fiber completeness remains a separate geometric input.
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


open SchemeBadAffineCover
variable [IsAffine U.toScheme]
attribute [local instance] originalBadAtlasNoetherian
local notation "BC" => badCover Lgood
open AffineValuationGeneratorLift IsLocalRing
local notation "g" => F ≫ U.ι ≫ normalizedFullRelationFirst f hL d V c k n o ≫
  A.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ R))
local instance originalExactCenterIntegerFiniteType : LocallyOfFiniteType g :=
  originalSource_doubleRelation_integer_finiteType f hL d V c k n o U
local notation "Zbad" => originalSourceBoundaryObstruction f hL d V c k n o W U hU hUW
local notation "zbad" => originalSourceBoundaryObstructionMap f hL d V c k n o W U hU hUW

open OriginalPrimeIntegralFiber
local notation "gens" => originalSourceBadChartGenerators f hL d V c k n o W U hU hUW

/-- A failed original chart constructs a finite generator pole at the exact contracted prime. -/
theorem originalSource_exact_center_integral_obstruction (P : PrimeSpectrum Tsource)
    (idx : (BC).I₀)
    (h : ¬ (localizedMap (badChartScalar σR Lgood idx)
      (PrimeSpectrum.comap κ P).asIdeal).IsIntegral) :
    ∃ S : ValuativeCommSq (scalarMorphism (badChartScalar σR Lgood idx)),
      S.i₂ (closedPoint S.R) = PrimeSpectrum.comap κ P ∧
      ∃ t ∈ gens idx, genericCoordinates (badChartScalar σR Lgood idx) S t ∉
        (algebraMap S.R S.K).range :=
  badChart_exact_center_obstruction σR Lgood g (PrimeSpectrum.comap κ P) idx h

/-- The exact original scalar center suffices to test full bad-chart local integrality. -/
theorem originalSource_integral_iff_exact_center_regular (P : PrimeSpectrum Tsource)
    (idx : (BC).I₀) :
    (localizedMap (badChartScalar σR Lgood idx)
      (PrimeSpectrum.comap κ P).asIdeal).IsIntegral ↔
      ∀ S : ValuativeCommSq (scalarMorphism (badChartScalar σR Lgood idx)),
        S.i₂ (closedPoint S.R) = PrimeSpectrum.comap κ P →
        ∀ t ∈ gens idx, genericCoordinates (badChartScalar σR Lgood idx) S t ∈
          (algebraMap S.R S.K).range :=
  badChart_integral_iff_exact_center_regular σR Lgood g (PrimeSpectrum.comap κ P) idx

/-- Exact-center regularity recovers exact original equations and an avoiding product. -/
theorem originalSource_equations_of_exact_center_regular (P : PrimeSpectrum Tsource)
    (hg : ∀ (idx : (BC).I₀)
      (S : ValuativeCommSq (scalarMorphism (badChartScalar σR Lgood idx))),
      S.i₂ (closedPoint S.R) = PrimeSpectrum.comap κ P →
        ∀ t ∈ gens idx, genericCoordinates (badChartScalar σR Lgood idx) S t ∈
          (algebraMap S.R S.K).range) :
    ∃ poly : ∀ idx : (BC).I₀, gens idx → Polynomial Ω,
      (∀ (idx : (BC).I₀) (t : gens idx),
        (poly idx t).eval₂ (badChartScalar σR Lgood idx) t.val = 0) ∧
      κ (badChartLeadingProduct σR Lgood g poly) ∉ P.asIdeal :=
  badCharts_equations_of_exact_center_regular σR Lgood g (PrimeSpectrum.comap κ P) hg

/-- One exact-center regularity test constructs a common open on which every chart square lifts. -/
theorem originalSource_lift_neighborhood_of_exact_center_regular (P : PrimeSpectrum Tsource)
    (hg : ∀ (idx : (BC).I₀)
      (S : ValuativeCommSq (scalarMorphism (badChartScalar σR Lgood idx))),
      S.i₂ (closedPoint S.R) = PrimeSpectrum.comap κ P →
        ∀ t ∈ gens idx, genericCoordinates (badChartScalar σR Lgood idx) S t ∈
          (algebraMap S.R S.K).range) :
    ∃ a : Ω, κ a ∉ P.asIdeal ∧ ∀ (idx : (BC).I₀)
      (S : ValuativeCommSq (scalarMorphism (badChartScalar σR Lgood idx))),
      a ∉ (S.i₂ (closedPoint S.R)).asIdeal → S.commSq.HasLift :=
  badCharts_lift_neighborhood_of_exact_center_regular σR Lgood g
    (PrimeSpectrum.comap κ P) hg

end FLT.Mazur.HilbertChart.AffineRestriction
