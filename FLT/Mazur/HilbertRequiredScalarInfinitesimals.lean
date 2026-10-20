/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertRequiredScalarImage
public import FLT.Mazur.ScalarPrimeThickenings

/-!
# Exact original relation equations at every required scalar prime

An actual whole-complete chart exists at each boundary-source contraction.
The same chart equalizes its full original relation on every centered scalar
test, including all constructed positive local infinitesimal orders.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Topology
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient SchemeOpenEnvelope
open RelativeRelationOrbit SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "q" => Over.Hom.left (snd f hL d V c k)
local notation "e" => fullRelationSchemeEquivalence f hL d V c k
attribute [local irreducible] relation fst snd equivalence

local notation "eo" => equivalence f hL d V c k
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
local notation "E" => (pullOpen eo W).val
local notation "Ω" => (invariantSheaf eo).obj.obj (op W)
local notation "s" => orbitScalarCoordinates eo W

attribute [local irreducible] invariantSheaf orbitScalarCoordinates
  EquivalenceRelationNormalizedFrames.source first completeInterior Complete
  scalarMorphism finiteTargetOpen

local notation "K" P => scalarResidueClosure P
local notation "t" P => Spec.map (CommRingCat.ofHom (algebraMap Ω (K P)))
attribute [local irreducible] scalarResidueClosureField scalarResidueClosureAlgebra

local notation "ec" => originalClosedEquivalence f hL d V c k
local notation "m" => originalClosedInvariantMap f hL d V c k
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
local notation "T" => (sourceSheaf ec).obj.obj (op Wc)
local notation "κ" => ((invariantInclusion ec).hom.app (op Wc)).hom.comp
  (originalClosedSectionPullback f hL d V c k W)
attribute [local irreducible] originalClosedEquivalence originalClosedInvariantMap
  originalClosedSectionPullback originalAmbientBoundaryRestriction

local notation "Chart" => OriginalScalarAffineChart f hL d V c k W

variable {f hL d V c k W}

/-- Exact equations on the unchanged full relation after an actual scalar base change. -/
@[irreducible] def OriginalScalarAffineChart.scalarTestEqualizes (C : Chart)
    {Y : Scheme} (b : Y ⟶ Spec (.of Ω)) : Prop :=
  let _ : IsAffine C.domain.toScheme := C.affine
  let ρ := restrictedAction
    (normalizedFullRelationAction f hL d V c k C.size C.label) C.domain C.stable
  let σ := normalizedOriginalScalarMap f hL d V c k C.size C.label W
    C.domain C.stable C.overDomain
  let j := C.domain.ι ≫ normalizedFullRelationFirst f hL d V c k C.size C.label
  ∀ a : invariantCoordinates ρ,
    (scalarTestRelationMap e (Fin C.size) C.label C.domain C.stable σ b ≫
      SchemeRelationRestriction.fst p q j).appTop a.val =
    (scalarTestRelationMap e (Fin C.size) C.label C.domain C.stable σ b ≫
      SchemeRelationRestriction.snd p q j).appTop a.val

/-- Every test supported in a chart's whole-complete scalar locus has exact relation equations. -/
theorem OriginalScalarAffineChart.scalarTestEqualizes_of_support (C : Chart)
    {Y : Scheme} (b : Y ⟶ Spec (.of Ω)) (hb : ∀ y : Y, b y ∈ C.wholeLocus) :
    C.scalarTestEqualizes b := by
  let _ : IsAffine C.domain.toScheme := C.affine
  let _ := selectedHilbertSource_isLocallyNoetherian f d V k
  rw [OriginalScalarAffineChart.scalarTestEqualizes]
  intro a
  apply wholeScalar_testRelation_equalizes
  intro y
  simpa only [OriginalScalarAffineChart.wholeLocus] using hb y

variable (f hL d V c k W)

/-- One actual chart at every required prime works on all scalar tests centered at that prime. -/
theorem exists_originalBoundaryPrime_centered_equation_chart (hW : IsAffineOpen E)
    (P : PrimeSpectrum T) :
    ∃ C : Chart, PrimeSpectrum.comap κ P ∈ C.wholeLocus ∧
      ∀ {Y : Scheme} (b : Y ⟶ Spec (.of Ω)),
        (∀ y : Y, b y = PrimeSpectrum.comap κ P) → C.scalarTestEqualizes b := by
  obtain ⟨C, hC⟩ := exists_originalBoundaryPrime_wholeScalar_chart f hL d V c k W hW P
  refine ⟨C, hC, fun b hb ↦ C.scalarTestEqualizes_of_support b ?_⟩
  intro y
  rw [hb y]
  exact hC

open ScalarPrimeThickenings

/-- A single actual required-prime chart works at every positive local infinitesimal order. -/
theorem exists_originalBoundaryPrime_infinitesimal_equation_chart (hW : IsAffineOpen E)
    (P : PrimeSpectrum T) :
    ∃ C : Chart, PrimeSpectrum.comap κ P ∈ C.wholeLocus ∧
      ∀ order : ℕ, C.scalarTestEqualizes
        (Spec.map (CommRingCat.ofHom (primeThickeningMap (PrimeSpectrum.comap κ P) order))) := by
  obtain ⟨C, hC, hc⟩ :=
    exists_originalBoundaryPrime_centered_equation_chart f hL d V c k W hW P
  refine ⟨C, hC, fun order ↦ hc _ ?_⟩
  intro y
  exact primeThickening_center (PrimeSpectrum.comap κ P) order y

end FLT.Mazur.HilbertChart.AffineRestriction
