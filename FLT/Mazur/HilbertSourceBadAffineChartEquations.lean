/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceBadAffineChartLifts
public import FLT.Mazur.HilbertSourceConstructedBoundaryUnitCover
public import FLT.Mazur.SchemeBadAffineCoverEquations

/-!
# Original Hilbert denominators from equations on the finite bad atlas

The affine bad charts and their finite original scalar generators are derived
from the family. Equations with nonvanishing leading product and complete
original fibers supply full source lifts. A boundary unit leading product
supplies a finite boundary denominator equation when all those fibers are complete.
The polynomial equations and that unit condition remain explicit inputs.
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
attribute [local irreducible] badChartGenerators
variable [IsAffine U.toScheme]
attribute [local instance] originalBadAtlasNoetherian
  originalSource_doubleRelation_integer_finiteType
local notation "gZ" => F ≫ U.ι ≫ normalizedFullRelationFirst f hL d V c k n o ≫
  A.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ R))
local notation "BC" => badCover Lgood
local notation "G" => badChartGenerators σR Lgood gZ
/-- Finite equations on the actual bad atlas prove safety at the unchanged boundary prime. -/
theorem originalSource_safe_of_badChart_equations
    (eqs : ∀ idx : (BC).I₀, G idx → Polynomial Ω)
    (heq : ∀ idx (a : G idx), (eqs idx a).eval₂ (badChartScalar σR Lgood idx) a.val = 0)
    (P : Ideal Tsource) [P.IsPrime]
    (hlead : κ (badChartLeadingProduct σR Lgood gZ eqs) ∉ P)
    (hP : ∀ x : U.toScheme, scalarMorphism σ₀ x = PrimeSpectrum.comap κ ⟨P, inferInstance⟩ →
      U.ι x ∈ completePointLocus («p» := p) («q» := q) (Fin n) o) :
    PrimeSpectrum.comap κ ⟨P, inferInstance⟩ ∈ scalarNeighborhoodLocus σR Lgood :=
  (mem_scalarNeighborhoodLocus_iff_badChart_equations σR Lgood gZ eqs
    (PrimeSpectrum.comap κ ⟨P, inferInstance⟩) heq hlead).mpr
      (originalSourceGoodRelationOpen_scalar_fiber f hL d V c k n o W U hU hUW P hP)

/-- The finite actual bad-chart equations give localized full source surjectivity. -/
theorem originalSource_surjective_of_badChart_equations
    (eqs : ∀ idx : (BC).I₀, G idx → Polynomial Ω)
    (heq : ∀ idx (a : G idx), (eqs idx a).eval₂ (badChartScalar σR Lgood idx) a.val = 0)
    (P : Ideal Tsource) [P.IsPrime]
    (hlead : κ (badChartLeadingProduct σR Lgood gZ eqs) ∉ P)
    (hP : ∀ x : U.toScheme, scalarMorphism σ₀ x = PrimeSpectrum.comap κ ⟨P, inferInstance⟩ →
      U.ι x ∈ completePointLocus («p» := p) («q» := q) (Fin n) o) :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
    Function.Surjective
      (originalSourceLocalizedCompatibleBoundaryMap f hL d V c k n o W U hU hUW P) :=
  originalSource_constructedOpen_surjective f hL d V c k n o W U hU hUW
    (show IsAffine U.toScheme from inferInstance) P
    (originalSource_safe_of_badChart_equations f hL d V c k n o W U hU hUW
      eqs heq P hlead hP)

/-- A boundary unit leading product turns the actual finite equations into a denominator cover. -/
theorem originalSource_finite_unit_equation_of_badChart_equations
    (eqs : ∀ idx : (BC).I₀, G idx → Polynomial Ω)
    (heq : ∀ idx (a : G idx), (eqs idx a).eval₂ (badChartScalar σR Lgood idx) a.val = 0)
    (hunit : IsUnit (κ (badChartLeadingProduct σR Lgood gZ eqs)))
    (hP : ∀ (P : PrimeSpectrum Tsource) (x : U.toScheme),
      scalarMorphism σ₀ x = PrimeSpectrum.comap κ P →
        U.ι x ∈ completePointLocus («p» := p) («q» := q) (Fin n) o) :
    ∃ (m' : ℕ) (a : Fin m' → Ω) (weights : Fin m' → Tsource),
      (∀ idx, (D).basicOpen (σR (a idx)) ≤ Lgood) ∧
        ∑ idx, weights idx * κ (a idx) = 1 := by
  apply (originalSource_all_primes_safe_iff_finite_equation
    f hL d V c k n o W U hU hUW).mp
  intro P
  apply originalSource_safe_of_badChart_equations f hL d V c k n o W U hU hUW eqs heq P.asIdeal
  · intro hm
    exact P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm hunit)
  · exact hP P

end FLT.Mazur.HilbertChart.AffineRestriction
