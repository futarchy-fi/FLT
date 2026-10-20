/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertScalarChartBoundaryPullback
public import FLT.Mazur.HilbertOrbitBoundaryFiniteOriginalLift

/-!
# Scalar-chart lifts on tests over the original boundary source

The scalar chart is an actual member of the original exhaustive atlas. Its
lift has the prescribed boundary value on every test over the original
boundary source, before or after scalar change.
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
attribute [local irreducible] originalClosedEquivalence
  normalizedOriginalBoundaryAction
  normalizedOriginalScalarMap

namespace OriginalScalarAffineChart
variable {f hL d V c k W} (C : OriginalScalarAffineChart f hL d V c k W)
local notation "ρ" => restrictedAction
  (normalizedFullRelationAction f hL d V c k C.size C.label) C.domain C.stable
local notation "σ" => normalizedOriginalScalarMap f hL d V c k C.size C.label W
  C.domain C.stable C.overDomain
local notation "j" => C.domain.ι ≫ normalizedFullRelationFirst f hL d V c k C.size C.label

/-- The scalar chart as actual data in the original exhaustive orbit atlas. -/
def toOrbitChart : OrbitBoundaryAtlas.Chart f hL d V c k W where
  size := C.size
  label := C.label
  domain := C.domain
  affine := C.affine
  stable := C.stable
  overDomain := C.overDomain

/-- The chart map into the unchanged original source domain. -/
abbrev originalSourceMap := OrbitBoundaryAtlas.chartMap f hL d V c k W C.toOrbitChart

local notation "Ec" => (pullOpen ec Wc).val
local notation "i" => originalBoundarySourceMap f hL d V c k
local notation "z" => originalClosedArrow f hL d V c k
local notation "g₀" => (openSourceMap eo ec i z
  (originalClosedArrow_fst f hL d V c k) (originalClosedArrow_snd f hL d V c k) W).left
open InvariantOpenRelationDiagram
attribute [local irreducible] RelativeRelationOrbit.openSourceMap
  InvariantOpenRelationDiagram.orbitFunctions

/-- The ambient lift agrees with the original section on every boundary-source test. -/
theorem boundaryLift_original_test (t : (invariantSheaf ec).obj.obj (op Wc))
    {Y : Scheme} (u : Y ⟶ C.domain.toScheme) (w : Y ⟶ (Ec).toScheme)
    (hu : u ≫ C.originalSourceMap = w ≫ g₀) :
    u.appTop (C.boundaryLift t).val = w.appTop (orbitFunctions ec Wc t).val := by
  have hw : u ≫ C.domain.ι ≫ first p q (Fin C.size) C.label =
      w ≫ (Ec).ι ≫ (i).left := by
    have h := congrArg (fun φ ↦ φ ≫ (E).ι) hu
    simpa only [originalSourceMap, Category.assoc, OrbitBoundaryAtlas.chartMap_inclusion,
      OrbitBoundaryAtlas.boundaryMap_inclusion, toOrbitChart, normalizedFullRelationFirst] using h
  apply InvariantBoundary.boundary_coefficient_test C.label (i).left C.domain Ec u w hw
    (normalizedOrbitBoundary_domain_le f hL d V c k C.size C.label W
      C.domain C.overDomain) (C.boundaryLift t).val (orbitFunctions ec Wc t).val
  simpa only [boundaryValue, normalizedOrbitBoundaryCoefficient_val,
    boundaryInclusion, normalizedOriginalBoundaryInclusion, normalizedOriginalBoundaryEndpoint]
    using C.boundaryLift_restrict t

open SchemeScalarRelationPullback
variable {Y : Scheme} (b : Y ⟶ Spec (.of
  ((invariantSheaf (equivalence f hL d V c k)).obj.obj (op W))))

/-- The actual scalar-test source still maps into the unchanged original source. -/
abbrev testOriginalMap := pullback.fst C.sourceScalars b ≫ C.originalSourceMap

/-- The full test-invariant lift has the prescribed value on every original boundary test. -/
theorem testBoundaryLift_original_test (hb : ∀ y : Y, b y ∈ C.wholeLocus)
    (t : (invariantSheaf ec).obj.obj (op Wc))
    {Z : Scheme} (u : Z ⟶ testSource C.sourceScalars b) (w : Z ⟶ (Ec).toScheme)
    (hu : u ≫ C.testOriginalMap b = w ≫ g₀) :
    u.appTop (C.testBoundaryLift b hb t).val = w.appTop (orbitFunctions ec Wc t).val := by
  change u.appTop ((pullback.fst C.sourceScalars b).appTop (C.boundaryLift t).val) = _
  simp only [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop]
  apply C.boundaryLift_original_test t (u ≫ pullback.fst C.sourceScalars b) w
  simpa only [Category.assoc] using hu

end OriginalScalarAffineChart
end FLT.Mazur.HilbertChart.AffineRestriction
