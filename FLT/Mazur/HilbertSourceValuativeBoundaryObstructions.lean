/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceClosedBoundaryObstructions
public import FLT.Mazur.SchemeBadAffineCoverValuation
public import FLT.Mazur.ValuationPoleEquations

/-!
# Actual valuative obstructions at the unchanged Hilbert boundary

Bad chart obstruction points produce valuation squares with incomplete
original generic endpoints. Exact-fiber completeness forces a finite pole
with a reciprocal vanishing at the center; all its polynomial leading
coefficients contract into the original prime. Regularity remains to be proved.
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
local instance originalValuationIntegerFiniteType : LocallyOfFiniteType g :=
  originalSource_doubleRelation_integer_finiteType f hL d V c k n o U
local notation "Zbad" => originalSourceBoundaryObstruction f hL d V c k n o W U hU hUW
local notation "zbad" => originalSourceBoundaryObstructionMap f hL d V c k n o W U hU hUW

/-- The finite generators are fixed before selecting a boundary prime or valuation. -/
def originalSourceBadChartGenerators (idx : (BC).I₀) : Finset Γ((BC).X idx, ⊤) :=
  badChartGenerators σR Lgood g idx

/-- The fixed actual generators span over the unchanged original invariant scalars. -/
theorem originalSourceBadChartGenerators_generate (idx : (BC).I₀) :
    Subring.closure (Set.range (badChartScalar σR Lgood idx) ∪
      (originalSourceBadChartGenerators f hL d V c k n o W U hU hUW idx : Set _)) = ⊤ :=
  badChartGenerators_generate σR Lgood g idx

local notation "gens" => originalSourceBadChartGenerators f hL d V c k n o W U hU hUW

/-- Every actual closed boundary obstruction has a valuative witness on the same bad chart. -/
theorem originalSource_closed_obstruction_has_valuation (idx : (BC).I₀) (x : Zbad idx) :
    ∃ S : ValuativeCommSq (scalarMorphism (badChartScalar σR Lgood idx)),
      S.i₂ (closedPoint S.R) = PrimeSpectrum.comap κ (zbad idx x) :=
  boundaryChart_point_has_valuation σR Lgood κ idx x

/-- The generic endpoint of every actual bad-chart valuation square is incomplete. -/
theorem originalSource_bad_valuation_generic_incomplete (idx : (BC).I₀)
    (S : ValuativeCommSq (scalarMorphism (badChartScalar σR Lgood idx))) :
    (F ≫ U.ι) (badChartMap Lgood idx (S.i₁ default)) ∉
      completePointLocus («p» := p) («q» := q) (Fin n) o :=
  originalSource_badChart_first_incomplete f hL d V c k n o U hU idx (S.i₁ default)

/-- Exact-fiber completeness forces an actual finite pole with a vanishing reciprocal. -/
theorem originalSource_closed_obstruction_reciprocal (idx : (BC).I₀) (x : Zbad idx)
    (hf : ∀ y : U.toScheme, scalarMorphism σ₀ y = PrimeSpectrum.comap κ (zbad idx x) →
      U.ι y ∈ completePointLocus («p» := p) («q» := q) (Fin n) o) :
    ∃ S : ValuativeCommSq (scalarMorphism (badChartScalar σR Lgood idx)),
      S.i₂ (closedPoint S.R) = PrimeSpectrum.comap κ (zbad idx x) ∧
      ∃ t ∈ gens idx, ∃ v : S.R, residue S.R v = 0 ∧
        algebraMap S.R S.K v * genericCoordinates (badChartScalar σR Lgood idx) S t = 1 := by
  apply boundaryChart_point_has_reciprocal σR Lgood κ g idx x
  exact originalSourceGoodRelationOpen_scalar_fiber f hL d V c k n o W U hU hUW
    (zbad idx x).asIdeal hf

/-- Every pole equation has original leading coefficient vanishing at the same boundary prime. -/
theorem originalSource_valuation_pole_leadingCoeff (idx : (BC).I₀) (P : PrimeSpectrum Tsource)
    (S : ValuativeCommSq (scalarMorphism (badChartScalar σR Lgood idx)))
    (hcenter : S.i₂ (closedPoint S.R) = PrimeSpectrum.comap κ P)
    (t : Γ((BC).X idx, ⊤))
    (ht : genericCoordinates (badChartScalar σR Lgood idx) S t ∉ (algebraMap S.R S.K).range)
    (poly : Polynomial Ω) (he : poly.eval₂ (badChartScalar σR Lgood idx) t = 0) :
    κ poly.leadingCoeff ∈ P.asIdeal := by
  have hm := ValuationPoleReciprocal.original_leadingCoeff_mem S.R S.K
    (badChartScalar σR Lgood idx) (centerCoordinates (badChartScalar σR Lgood idx) S)
    (genericCoordinates (badChartScalar σR Lgood idx) S)
    (coordinates_comm (badChartScalar σR Lgood idx) S) t ht poly he
  change poly.leadingCoeff ∈ (maximalIdeal S.R).comap
    (centerCoordinates (badChartScalar σR Lgood idx) S) at hm
  rw [center_comap_maximalIdeal, hcenter] at hm
  exact hm

/-- Whole exact-fiber completeness and finite valuation regularity give original-prime avoidance. -/
theorem originalSource_safe_of_regular_generators (P : PrimeSpectrum Tsource)
    (hf : ∀ y : U.toScheme, scalarMorphism σ₀ y = PrimeSpectrum.comap κ P →
      U.ι y ∈ completePointLocus («p» := p) («q» := q) (Fin n) o)
    (hg : ∀ (idx : (BC).I₀)
      (S : ValuativeCommSq (scalarMorphism (badChartScalar σR Lgood idx))),
      S.i₂ (closedPoint S.R) = PrimeSpectrum.comap κ P →
        ∀ t ∈ gens idx, genericCoordinates (badChartScalar σR Lgood idx) S t ∈
          (algebraMap S.R S.K).range) :
    PrimeSpectrum.comap κ P ∈ scalarNeighborhoodLocus σR Lgood :=
  scalar_safe_of_regular_generators σR Lgood κ g P
    (originalSourceGoodRelationOpen_scalar_fiber f hL d V c k n o W U hU hUW P.asIdeal hf) hg

/-- Finite regularity tests yield full compatible source lifts at the original prime. -/
theorem originalSource_surjective_of_regular_generators (P : PrimeSpectrum Tsource)
    (hf : ∀ y : U.toScheme, scalarMorphism σ₀ y = PrimeSpectrum.comap κ P →
      U.ι y ∈ completePointLocus («p» := p) («q» := q) (Fin n) o)
    (hg : ∀ (idx : (BC).I₀)
      (S : ValuativeCommSq (scalarMorphism (badChartScalar σR Lgood idx))),
      S.i₂ (closedPoint S.R) = PrimeSpectrum.comap κ P →
        ∀ t ∈ gens idx, genericCoordinates (badChartScalar σR Lgood idx) S t ∈
          (algebraMap S.R S.K).range) :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
    Function.Surjective
      (originalSourceLocalizedCompatibleBoundaryMap f hL d V c k n o W U hU hUW P.asIdeal) :=
  originalSource_constructedOpen_surjective f hL d V c k n o W U hU hUW
    (show IsAffine U.toScheme from inferInstance) P.asIdeal
    (originalSource_safe_of_regular_generators f hL d V c k n o W U hU hUW P hf hg)

end FLT.Mazur.HilbertChart.AffineRestriction
