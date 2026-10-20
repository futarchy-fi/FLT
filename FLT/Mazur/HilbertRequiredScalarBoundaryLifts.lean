/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertScalarChartBoundaryPullback
public import FLT.Mazur.ScalarPrimeThickeningTransitions

/-!
# Coherent actual boundary lifts at every required scalar prime

One finite family of actual charts suffices for every original boundary
contraction. On the chosen chart, every original boundary section lifts to
all full infinitesimal relation equalizers, coherently under every transition.
No inverse limit or original scalar-local boundary surjectivity is asserted.
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

local notation "ec" => originalClosedEquivalence f hL d V c k
local notation "m" => originalClosedInvariantMap f hL d V c k
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
local notation "T" => (sourceSheaf ec).obj.obj (op Wc)
local notation "κ" => ((invariantInclusion ec).hom.app (op Wc)).hom.comp
  (originalClosedSectionPullback f hL d V c k W)
attribute [local irreducible] originalClosedEquivalence originalClosedInvariantMap
  originalClosedSectionPullback originalAmbientBoundaryRestriction

local notation "Chart" => OriginalScalarAffineChart f hL d V c k W

open ScalarPrimeThickenings SchemeScalarRelationPullback
local notation "Q" P:max => PrimeSpectrum.comap κ P
attribute [local irreducible] OriginalScalarAffineChart.testBoundaryMap
  OriginalScalarAffineChart.testBoundaryLift OriginalScalarAffineChart.testBoundaryValue
  SchemeScalarRelationPullback.testInvariants SchemeScalarRelationPullback.invariantChange

namespace OriginalScalarAffineChart
variable {f hL d V c k W} (C : OriginalScalarAffineChart f hL d V c k W)
  (P : PrimeSpectrum ((invariantSheaf (equivalence f hL d V c k)).obj.obj (op W)))

/-- The original boundary image lifts through every full scalar-test equalizer centered here. -/
@[irreducible] def LiftsCenteredTests : Prop :=
  ∀ {Y : Scheme} (b : Y ⟶ Spec (.of Ω)), (∀ y : Y, b y = P) →
    ∀ t : (invariantSheaf ec).obj.obj (op Wc),
      ∃ v : C.testInvariantRing b, C.testBoundaryMap b v = C.testBoundaryValue b t

/-- The actual chart geometry supplies these lifts for every original boundary section. -/
theorem liftsCenteredTests_of_mem (hP : P ∈ C.wholeLocus) : C.LiftsCenteredTests P := by
  rw [LiftsCenteredTests]
  intro Y b hb t
  have hs : ∀ y, b y ∈ C.wholeLocus := fun y ↦ (hb y) ▸ hP
  exact ⟨C.testBoundaryLift b hs t, C.testBoundaryLift_spec b hs t⟩

/-- Exact full relation boundary lifts at all orders, with every actual transition equation. -/
@[irreducible] def CoherentPrimeBoundaryLifts : Prop :=
  ∀ t : (invariantSheaf ec).obj.obj (op Wc),
    ∃ v : ∀ order : ℕ, C.testInvariantRing (primeThickeningTest P order),
      (∀ order, C.testBoundaryMap (primeThickeningTest P order) (v order) =
        C.testBoundaryValue (primeThickeningTest P order) t) ∧
      ∀ lo hi : ℕ, ∀ h : lo ≤ hi,
        invariantChange C.fullFirst C.fullSecond C.sourceScalars C.full_scalar_square
          (primeThickeningTest P hi) (primeThickeningTest P lo)
          (primeThickeningInclusion P h) (primeThickeningInclusion_scalars P h) (v hi) = v lo

/-- One ambient chart lift constructs the whole coherent family without a limit hypothesis. -/
theorem coherentPrimeBoundaryLifts_of_mem (hP : P ∈ C.wholeLocus) :
    C.CoherentPrimeBoundaryLifts P := by
  rw [CoherentPrimeBoundaryLifts]
  intro t
  have hs (order : ℕ) : ∀ x, primeThickeningTest P order x ∈ C.wholeLocus := by
    intro x
    change PrimeSpectrum.comap (primeThickeningMap P order) x ∈ C.wholeLocus
    rw [primeThickening_center]
    exact hP
  refine ⟨fun order ↦ C.testBoundaryLift _ (hs order) t,
    fun order ↦ C.testBoundaryLift_spec _ (hs order) t, fun lo hi h ↦ ?_⟩
  exact C.testBoundaryLift_change _ _ (primeThickeningInclusion P h)
    (primeThickeningInclusion_scalars P h) (hs hi) (hs lo) t

end OriginalScalarAffineChart

/-- A finite chart family supplies coherent original boundary lifts at every required prime. -/
theorem exists_finite_originalBoundary_coherent_lifts (hW : IsAffineOpen E) :
    ∃ charts : Finset Chart, ∀ P : PrimeSpectrum T,
      ∃ C ∈ charts, Q P ∈ C.wholeLocus ∧ C.LiftsCenteredTests (Q P) ∧
        C.CoherentPrimeBoundaryLifts (Q P) := by
  obtain ⟨charts, hc⟩ := exists_finite_originalBoundary_wholeScalar_cover f hL d V c k W hW
  refine ⟨charts, fun P ↦ ?_⟩
  obtain ⟨C, hC, hP⟩ := hc P
  exact ⟨C, hC, hP, C.liftsCenteredTests_of_mem _ hP, C.coherentPrimeBoundaryLifts_of_mem _ hP⟩

end FLT.Mazur.HilbertChart.AffineRestriction
