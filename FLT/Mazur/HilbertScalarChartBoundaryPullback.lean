/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertScalarChartBoundaryData
public import FLT.Mazur.SchemeScalarRelationTransition

/-!
# Original boundary sections lift to actual scalar-test equalizers

The constructed element lives on the scalar pullback of the chart source,
and satisfies both endpoints of the entire pulled original relation. Its
boundary restriction is the original section on the actual boundary test.
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
attribute [local irreducible] originalClosedEquivalence originalClosedInvariantMap
  normalizedOriginalBoundaryInclusion normalizedOriginalBoundaryAction
  normalizedOriginalScalarMap

namespace OriginalScalarAffineChart
variable {f hL d V c k W} (C : OriginalScalarAffineChart f hL d V c k W)
local notation "ρ" => restrictedAction
  (normalizedFullRelationAction f hL d V c k C.size C.label) C.domain C.stable
local notation "σ" => normalizedOriginalScalarMap f hL d V c k C.size C.label W
  C.domain C.stable C.overDomain
local notation "j" => C.domain.ι ≫ normalizedFullRelationFirst f hL d V c k C.size C.label

open SchemeScalarRelationPullback
variable {Y : Scheme} (b : Y ⟶ Spec (.of
  ((invariantSheaf (equivalence f hL d V c k)).obj.obj (op W))))

/-- Actual full relation invariants on the chart's scalar-test source. -/
abbrev testInvariantRing : Subring Γ(testSource C.sourceScalars b, ⊤) :=
  testInvariants C.fullFirst C.fullSecond C.sourceScalars C.full_scalar_square b

/-- Restrict the full test equalizer to the actual original chart boundary test. -/
def testBoundaryMap : C.testInvariantRing b →+*
    Γ(pullback (C.boundaryInclusion ≫ C.sourceScalars) b, ⊤) :=
  testBoundaryRestriction C.fullFirst C.fullSecond C.sourceScalars C.full_scalar_square b
    C.boundaryInclusion

/-- The original boundary section on the unreduced scalar-test boundary. -/
def testBoundaryValue (t : (invariantSheaf ec).obj.obj (op Wc)) :
    Γ(pullback (C.boundaryInclusion ≫ C.sourceScalars) b, ⊤) :=
  (pullback.fst (C.boundaryInclusion ≫ C.sourceScalars) b).appTop (C.boundaryValue t)

/-- The same ambient boundary lift gives an actual full test-invariant coefficient. -/
def testBoundaryLift (hb : ∀ y : Y, b y ∈ C.wholeLocus)
    (t : (invariantSheaf ec).obj.obj (op Wc)) : C.testInvariantRing b :=
  invariantLift C.fullFirst C.fullSecond C.sourceScalars C.full_scalar_square b
    (C.boundaryLift t).val (C.boundaryLift_equalizes t b hb)

/-- This is the prescribed original boundary value, with all scalar-test nilpotents retained. -/
theorem testBoundaryLift_spec (hb : ∀ y : Y, b y ∈ C.wholeLocus)
    (t : (invariantSheaf ec).obj.obj (op Wc)) :
    C.testBoundaryMap b (C.testBoundaryLift b hb t) = C.testBoundaryValue b t := by
  unfold testBoundaryMap testBoundaryLift testBoundaryValue
  rw [testBoundaryRestriction_lift, boundaryLift_restrict]

/-- Every original boundary section lies in the image of the actual full test equalizer. -/
theorem testBoundaryValue_mem_range (hb : ∀ y : Y, b y ∈ C.wholeLocus)
    (t : (invariantSheaf ec).obj.obj (op Wc)) :
    C.testBoundaryValue b t ∈ (C.testBoundaryMap b).range :=
  ⟨C.testBoundaryLift b hb t, C.testBoundaryLift_spec b hb t⟩

variable {Y' : Scheme} (b' : Y' ⟶ Spec (.of
  ((invariantSheaf (equivalence f hL d V c k)).obj.obj (op W))))
  (g : Y' ⟶ Y) (hg : g ≫ b = b')

/-- These actual lifts are coherent along every supported scalar-test morphism. -/
theorem testBoundaryLift_change (hb : ∀ y : Y, b y ∈ C.wholeLocus)
    (hb' : ∀ y : Y', b' y ∈ C.wholeLocus)
    (t : (invariantSheaf ec).obj.obj (op Wc)) :
    invariantChange C.fullFirst C.fullSecond C.sourceScalars C.full_scalar_square b b' g hg
        (C.testBoundaryLift b hb t) = C.testBoundaryLift b' hb' t :=
  invariantChange_lift C.fullFirst C.fullSecond C.sourceScalars C.full_scalar_square b b' g hg
    (C.boundaryLift t).val (C.boundaryLift_equalizes t b hb) (C.boundaryLift_equalizes t b' hb')

end OriginalScalarAffineChart
end FLT.Mazur.HilbertChart.AffineRestriction
