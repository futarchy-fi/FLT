/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceFiniteCompletenessTests
public import FLT.Mazur.SchemeFiniteGroupBoundaryCompleteness

/-!
# Full original boundary completeness as finite nilpotence equations

The original scalar boundary product is constructed without reducing it.
Universal completeness of the actual normalized chart fibers is equivalent
to one common power annihilating the fixed support functions on that product.
These nilpotence equations remain the geometric input to prove.
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


open SchemeBadAffineCover
variable [IsAffine U.toScheme]
attribute [local instance] originalBadAtlasNoetherian
local notation "BC" => badCover Lgood
open AffineValuationGeneratorLift IsLocalRing
local notation "g" => F ≫ U.ι ≫ normalizedFullRelationFirst f hL d V c k n o ≫
  A.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ R))
local instance originalBoundaryTestsIntegerFiniteType : LocallyOfFiniteType g :=
  originalSource_doubleRelation_integer_finiteType f hL d V c k n o U
local notation "Zbad" => originalSourceBoundaryObstruction f hL d V c k n o W U hU hUW
local notation "zbad" => originalSourceBoundaryObstructionMap f hL d V c k n o W U hU hUW

open OriginalPrimeIntegralFiber
local notation "gens" => originalSourceBadChartGenerators f hL d V c k n o W U hU hUW

local instance originalBoundaryCompletenessNoetherian :
    TopologicalSpace.NoetherianSpace U.toScheme := by
  let _ := originalSource_affine_isNoetherian f hL d V c k n o U
    (show IsAffine U.toScheme from inferInstance)
  infer_instance

open AffineScalarBoundaryNilpotence
attribute [local irreducible] boundaryProduct boundaryCoordinate
local notation "tests" => originalSourceCompletenessTests f hL d V c k n o U hU
local notation "C" => U.ι ⁻¹' completePointLocus («p» := p) («q» := q) (Fin n) o

/-- Universal whole-fiber completeness is exactly nilpotence of finitely many boundary functions. -/
theorem originalSource_all_complete_iff_boundary_nilpotent :
    (∀ (P : PrimeSpectrum Tsource) (x : U.toScheme),
      scalarMorphism σ₀ x = PrimeSpectrum.comap κ P →
        U.ι x ∈ completePointLocus («p» := p) («q» := q) (Fin n) o) ↔
      ∀ t ∈ tests, IsNilpotent (boundaryCoordinate σ κ t) :=
  all_scalar_fibers_subset_iff_boundary_nilpotent τU C (completeChart_isClosed (Fin n) o U)
    (completeChart_stable e (Fin n) o U hU) σ κ

/-- One common exponent tests completeness at all original boundary primes simultaneously. -/
theorem originalSource_all_complete_iff_boundary_power :
    (∀ (P : PrimeSpectrum Tsource) (x : U.toScheme),
      scalarMorphism σ₀ x = PrimeSpectrum.comap κ P →
        U.ι x ∈ completePointLocus («p» := p) («q» := q) (Fin n) o) ↔
      ∃ powN : ℕ, ∀ t ∈ tests, boundaryCoordinate σ κ t ^ powN = 0 :=
  all_scalar_fibers_subset_iff_boundary_power τU C (completeChart_isClosed (Fin n) o U)
    (completeChart_stable e (Fin n) o U hU) σ κ

/-- A failed fixed boundary function produces an actual incomplete frame over an exact prime. -/
theorem originalSource_incomplete_of_boundary_not_nilpotent
    (t : Sinv) (ht : t ∈ tests) (hn : ¬ IsNilpotent (boundaryCoordinate σ κ t)) :
    ∃ (P : PrimeSpectrum Tsource) (x : U.toScheme),
      scalarMorphism σ₀ x = PrimeSpectrum.comap κ P ∧
        U.ι x ∉ completePointLocus («p» := p) («q» := q) (Fin n) o := by
  by_contra h
  push Not at h
  exact hn ((originalSource_all_complete_iff_boundary_nilpotent
    f hL d V c k n o W U hU hUW).mp h t ht)

/-- Boundary nilpotence and centered regularity give original source lifts at every prime. -/
theorem originalSource_all_surjective_of_boundary_nilpotent
    (hn : ∀ t ∈ tests, IsNilpotent (boundaryCoordinate σ κ t))
    (hg : ∀ (P : PrimeSpectrum Tsource) (idx : (BC).I₀)
      (S : ValuativeCommSq (scalarMorphism (badChartScalar σR Lgood idx))),
      S.i₂ (closedPoint S.R) = PrimeSpectrum.comap κ P →
        ∀ t ∈ gens idx, genericCoordinates (badChartScalar σR Lgood idx) S t ∈
          (algebraMap S.R S.K).range)
    (P : PrimeSpectrum Tsource) :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
    Function.Surjective
      (originalSourceLocalizedCompatibleBoundaryMap f hL d V c k n o W U hU hUW P.asIdeal) := by
  apply originalSource_surjective_of_finite_equations_and_regular
    f hL d V c k n o W U hU hUW P
  · apply (originalSource_complete_fiber_iff_finite_equations
      f hL d V c k n o W U hU hUW P).mp
    exact (originalSource_all_complete_iff_boundary_nilpotent
      f hL d V c k n o W U hU hUW).mpr hn P
  · exact hg P

end FLT.Mazur.HilbertChart.AffineRestriction
