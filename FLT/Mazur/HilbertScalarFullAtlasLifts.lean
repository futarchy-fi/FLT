/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertScalarChartFullDescent

/-!
# Coherent original scalar-test lifts and full atlas corrections

The descended boundary lift is an actual element of the whole original test
equalizer. It yields corrections on the old full atlas, and its value is
compatible with arbitrary transitions of supported, covered scalar tests.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Topology
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient SchemeOpenEnvelope
open RelativeRelationOrbit SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] relativeFppfSheaf AmpleLineBundle
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
  originalBoundarySource originalBoundarySourceMap originalClosedRelation
  originalClosedFst originalClosedSnd originalClosedArrow
  normalizedOriginalBoundaryAction
  normalizedOriginalScalarMap

namespace OriginalScalarAffineChart
variable {f hL d V c k W} (C : OriginalScalarAffineChart f hL d V c k W)
local notation "ρ" => restrictedAction
  (normalizedFullRelationAction f hL d V c k C.size C.label) C.domain C.stable
local notation "σ" => normalizedOriginalScalarMap f hL d V c k C.size C.label W
  C.domain C.stable C.overDomain
local notation "j" => C.domain.ι ≫ normalizedFullRelationFirst f hL d V c k C.size C.label

open SchemeScalarRelationPullback SchemeFppfRelationDescent InvariantOpenRelationDiagram
variable {Y : Scheme} (b : Y ⟶ Spec (.of
  ((invariantSheaf (equivalence f hL d V c k)).obj.obj (op W))))
local notation "p₀" => OriginalScalarSource.first f hL d V c k W
local notation "q₀" => OriginalScalarSource.second f hL d V c k W
local notation "hs₀" => OriginalScalarSource.scalar_square f hL d V c k W
local notation "pt" => testFirst p₀ (scalarMorphism s) b
local notation "qt" => testSecond p₀ q₀ (scalarMorphism s) hs₀ b
local notation "cmp" => C.fullSourceComparison b
local notation "ri" => (relationInclusion (fst f hL d V c k) E).left
attribute [local irreducible] SchemeRelationRestriction.doubleDomain
  SchemeRelationRestriction.fst SchemeRelationRestriction.snd
  testFirst testSecond fullSourceComparison fullTestDescend
variable (hc : ∀ x : testSource
    (scalarMorphism (orbitScalarCoordinates (equivalence f hL d V c k) W)) b,
  pullback.fst (scalarMorphism (orbitScalarCoordinates (equivalence f hL d V c k) W)) b x ∈
    Set.range C.originalSourceMap)

variable (hb : ∀ y : Y, b y ∈ C.wholeLocus)
local notation "Ec" => (pullOpen ec Wc).val
local notation "i" => originalBoundarySourceMap f hL d V c k
local notation "z" => originalClosedArrow f hL d V c k
local notation "g₀" => (openSourceMap eo ec i z
  (originalClosedArrow_fst f hL d V c k) (originalClosedArrow_snd f hL d V c k) W).left
local notation "it" => testFirst g₀ (scalarMorphism s) b
attribute [local irreducible] RelativeRelationOrbit.openSourceMap
  InvariantOpenRelationDiagram.orbitFunctions

/-- The actual original test lift obtained by descending the prescribed chart coefficient. -/
def fullBoundaryLift (t : (invariantSheaf ec).obj.obj (op Wc)) :
    OriginalScalarSource.testRing f hL d V c k W b :=
  C.fullTestDescend b hc (C.testBoundaryLift b hb t)

/-- The full original boundary value of the descended lift. -/
theorem fullBoundaryLift_boundary (t : (invariantSheaf ec).obj.obj (op Wc)) :
    (it).appTop (C.fullBoundaryLift b hc hb t).val =
      OriginalScalarSource.originalTestBoundaryValue f hL d V c k W b t :=
  C.fullTestDescend_boundary b hc hb t

/-- The descended lift restricts to the original prescribed chart coefficient. -/
theorem fullBoundaryLift_chart (t : (invariantSheaf ec).obj.obj (op Wc)) :
    (cmp).appTop (C.fullBoundaryLift b hc hb t).val = (C.testBoundaryLift b hb t).val :=
  C.fullTestDescend_spec b hc (C.testBoundaryLift b hb t)

attribute [local irreducible] fullBoundaryLift testBoundaryLift

include C hc hb in
/-- The lift constructs exact boundary-kernel corrections on the entire old test atlas. -/
theorem fullAtlas_corrections
    (hW : IsAffineOpen (pullOpen (equivalence f hL d V c k) W).val)
    (t : (invariantSheaf ec).obj.obj (op Wc)) :
    ∃ corrections : ∀ a, Γ((OriginalScalarSource.atlas f hL d V c k W b hW).X a, ⊤),
      (∀ a, (pullback.snd it
        ((OriginalScalarSource.atlas f hL d V c k W b hW).f a)).appTop (corrections a) = 0) ∧
      Compatible pt qt (OriginalScalarSource.atlas f hL d V c k W b hW)
        (fun a ↦ OriginalScalarSource.oldTestLift f hL d V c k W b hW t a - corrections a) :=
  (OriginalScalarSource.originalTest_lift_iff_corrections f hL d V c k W b hW t).mp
    ⟨C.fullBoundaryLift b hc hb t, C.fullBoundaryLift_boundary b hc hb t⟩

variable {Y' : Scheme} (b' : Y' ⟶ Spec (.of
  ((invariantSheaf (equivalence f hL d V c k)).obj.obj (op W))))
  (g : Y' ⟶ Y) (hg : g ≫ b = b')

omit [Etale V.hom] in
/-- The actual chart/source comparison commutes with every scalar-test transition. -/
theorem fullSourceComparison_change :
    sourceChange C.sourceScalars b b' g hg ≫ C.fullSourceComparison b =
      C.fullSourceComparison b' ≫ sourceChange (scalarMorphism s) b b' g hg := by
  apply pullback.hom_ext
  · simp only [Category.assoc, fullSourceComparison_fst, sourceChange_fst,
      sourceChange_fst_assoc]
  · simp only [Category.assoc, fullSourceComparison_snd, sourceChange_snd,
      fullSourceComparison_snd_assoc]

/-- The covering chart determines the descended original invariant coefficient uniquely. -/
theorem fullTestDescend_unique (a : C.testInvariantRing b)
    (v : OriginalScalarSource.testRing f hL d V c k W b)
    (hv : (cmp).appTop v.val = a.val) : v = C.fullTestDescend b hc a := by
  unfold fullTestDescend
  exact (C.fullTestInvariant_existsUnique b hc a).choose_spec.2 v hv

omit [Etale V.hom] in
/-- Pullback of full original coefficients commutes with chart restriction. -/
theorem fullSourceComparison_change_app
    (v : OriginalScalarSource.testRing f hL d V c k W b) :
    (C.fullSourceComparison b').appTop
        (invariantChange p₀ q₀ (scalarMorphism s) hs₀ b b' g hg v).val =
      (sourceChange C.sourceScalars b b' g hg).appTop ((cmp).appTop v.val) := by
  change (C.fullSourceComparison b').appTop
    ((sourceChange (scalarMorphism s) b b' g hg).appTop v.val) = _
  simp only [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop]
  rw [← C.fullSourceComparison_change b b' g hg]

/-- Unique full-source descent commutes with a transition of compatible chart coefficients. -/
theorem fullTestDescend_change
    (hc' : ∀ x : testSource (scalarMorphism s) b',
      pullback.fst (scalarMorphism s) b' x ∈ Set.range C.originalSourceMap)
    (a : C.testInvariantRing b) (a' : C.testInvariantRing b')
    (ha : invariantChange C.fullFirst C.fullSecond C.sourceScalars C.full_scalar_square
      b b' g hg a = a') :
    invariantChange p₀ q₀ (scalarMorphism s) hs₀ b b' g hg (C.fullTestDescend b hc a) =
      C.fullTestDescend b' hc' a' := by
  apply C.fullTestDescend_unique b' hc' a'
  rw [fullSourceComparison_change_app, fullTestDescend_spec]
  exact congrArg Subtype.val ha

/-- Exact descent preserves coherence of the prescribed boundary lifts on the whole source. -/
theorem fullBoundaryLift_change
    (hc' : ∀ x : testSource (scalarMorphism s) b',
      pullback.fst (scalarMorphism s) b' x ∈ Set.range C.originalSourceMap)
    (hb' : ∀ y : Y', b' y ∈ C.wholeLocus)
    (t : (invariantSheaf ec).obj.obj (op Wc)) :
    invariantChange p₀ q₀ (scalarMorphism s) hs₀ b b' g hg (C.fullBoundaryLift b hc hb t) =
      C.fullBoundaryLift b' hc' hb' t := by
  unfold fullBoundaryLift
  exact C.fullTestDescend_change b hc b' g hg hc'
    (C.testBoundaryLift b hb t) (C.testBoundaryLift b' hb' t)
    (C.testBoundaryLift_change b b' g hg hb hb' t)

end OriginalScalarAffineChart
end FLT.Mazur.HilbertChart.AffineRestriction
