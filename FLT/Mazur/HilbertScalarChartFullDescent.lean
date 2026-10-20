/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertScalarChartSourceComparison
public import FLT.Mazur.SchemeScalarRestrictedTests
public import FLT.Mazur.HilbertOriginalScalarTestCorrections

/-!
# Descending actual chart boundary lifts to the full original scalar source

The existing chart lift descends with its exact original boundary value when
its actual original-source image covers the test. This supplies the descent
construction; the source image inclusion remains a geometric input.
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
  testFirst testSecond fullSourceComparison
variable (hc : ∀ x : testSource
    (scalarMorphism (orbitScalarCoordinates (equivalence f hL d V c k) W)) b,
  pullback.fst (scalarMorphism (orbitScalarCoordinates (equivalence f hL d V c k) W)) b x ∈
    Set.range C.originalSourceMap)

/-- The selected chart covers the full original scalar test under the exact image condition. -/
abbrev fullTestCover : (testSource (scalarMorphism s) b).Cover Scheme.fppfPrecoverage :=
  .singleton cmp (C.fullSourceComparison_covers b hc)

/-- Chart invariance gives all original mixed relation equations on this covering family. -/
theorem fullTestCover_compatible (a : C.testInvariantRing b) :
    Compatible pt qt (C.fullTestCover b hc) (fun _ ↦ a.val) := by
  intro T i l u v w hu hv
  change w ≫ pt = u ≫ cmp at hu
  change w ≫ qt = v ≫ cmp at hv
  apply restricted_invariant_test p q j C.sourceScalars C.full_scalar_square b a
    (w ≫ pullback.fst (p₀ ≫ scalarMorphism s) b ≫ ri) u v
  · have he := congrArg (fun z ↦ z ≫ pullback.fst (scalarMorphism s) b) hu
    simp only [Category.assoc, testFirst_fst, fullSourceComparison_fst] at he
    have he' := congrArg (fun z ↦ z ≫ (E).ι) he
    have hp := congrArg Over.Hom.left (inclusion_fst (fst f hL d V c k) E)
    change ri ≫ p = p₀ ≫ (E).ι at hp
    simpa only [Category.assoc, hp,
      OrbitBoundaryAtlas.chartMap_inclusion, originalSourceMap, toOrbitChart,
      normalizedFullRelationFirst] using he'
  · have he := congrArg (fun z ↦ z ≫ pullback.fst (scalarMorphism s) b) hv
    simp only [Category.assoc, testSecond_fst, fullSourceComparison_fst] at he
    have he' := congrArg (fun z ↦ z ≫ (E).ι) he
    have hq := congrArg Over.Hom.left (inclusion_snd (fst f hL d V c k)
      (snd f hL d V c k) E (pullOpen_preimage_eq eo W))
    change ri ≫ q = q₀ ≫ (E).ι at hq
    simpa only [Category.assoc, hq,
      OrbitBoundaryAtlas.chartMap_inclusion, originalSourceMap, toOrbitChart,
      normalizedFullRelationFirst] using he'
  · have h₁ := congrArg (fun z ↦ z ≫ pullback.snd (scalarMorphism s) b) hu
    have h₂ := congrArg (fun z ↦ z ≫ pullback.snd (scalarMorphism s) b) hv
    simp only [Category.assoc, testFirst, testSecond, pullback.lift_snd,
      fullSourceComparison_snd] at h₁ h₂
    exact h₁.symm.trans h₂

include hc

/-- The actual chart invariant descends uniquely to the full original test equalizer. -/
theorem fullTestInvariant_existsUnique (a : C.testInvariantRing b) :
    ∃! v : OriginalScalarSource.testRing f hL d V c k W b, (cmp).appTop v.val = a.val := by
  let er := OriginalScalarSource.fullEquivalence f hL d V c k W
  obtain ⟨v, hv, huniq⟩ := compatible_existsUnique pt qt (C.fullTestCover b hc)
    (testReflexivity _ _ b er.r er.reflexivity₁)
    (testReflexivity_first _ _ b er.r er.reflexivity₁)
    (testReflexivity_second _ _ _ _ b er.r er.reflexivity₁ er.reflexivity₂)
    (fun _ ↦ a.val) (C.fullTestCover_compatible b hc a)
  exact ⟨v, congrFun hv PUnit.unit, fun z hz ↦ huniq z (funext (fun _ ↦ hz))⟩

/-- The unique descended coefficient on the full original source. -/
def fullTestDescend (a : C.testInvariantRing b) :
    OriginalScalarSource.testRing f hL d V c k W b :=
  (C.fullTestInvariant_existsUnique b hc a).choose

/-- Descent recovers the prescribed coefficient on the chosen covering chart. -/
theorem fullTestDescend_spec (a : C.testInvariantRing b) :
    (cmp).appTop (C.fullTestDescend b hc a).val = a.val :=
  (C.fullTestInvariant_existsUnique b hc a).choose_spec.1

attribute [local irreducible] fullTestDescend

/-- Descent preserves any exact boundary tested on the covering chart. -/
theorem fullTestDescend_boundary_of_tests {Z : Scheme}
    (i : Z ⟶ testSource (scalarMorphism s) b) (a : C.testInvariantRing b) (t : Γ(Z, ⊤))
    (ht : HasBoundary (C.fullTestCover b hc) i (fun _ ↦ a.val) t) :
    i.appTop (C.fullTestDescend b hc a).val = t := by
  apply boundary_of_restriction pt qt (C.fullTestCover b hc) i
  intro l
  change (pullback.snd i cmp).appTop ((cmp).appTop (C.fullTestDescend b hc a).val) = _
  rw [fullTestDescend_spec]
  exact ht l

local notation "Ec" => (pullOpen ec Wc).val
local notation "i" => originalBoundarySourceMap f hL d V c k
local notation "z" => originalClosedArrow f hL d V c k
local notation "g₀" => (openSourceMap eo ec i z
  (originalClosedArrow_fst f hL d V c k) (originalClosedArrow_snd f hL d V c k) W).left
local notation "it" => testFirst g₀ (scalarMorphism s) b
attribute [local irreducible] RelativeRelationOrbit.openSourceMap
  InvariantOpenRelationDiagram.orbitFunctions testBoundaryLift

/-- The prescribed chart coefficient has the full original boundary on the covering test. -/
theorem fullTestCover_boundary (hb : ∀ y : Y, b y ∈ C.wholeLocus)
    (t : (invariantSheaf ec).obj.obj (op Wc)) :
    HasBoundary (C.fullTestCover b hc) it (fun _ ↦ (C.testBoundaryLift b hb t).val)
      (OriginalScalarSource.originalTestBoundaryValue f hL d V c k W b t) := by
  unfold HasBoundary
  intro l
  unfold OriginalScalarSource.originalTestBoundaryValue
  dsimp only [InvariantOpenRelationDiagram.source, Over.mk_left]
  change (pullback.snd it cmp).appTop (C.testBoundaryLift b hb t).val = _
  simp only [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop]
  apply C.testBoundaryLift_original_test b hb t (pullback.snd it cmp)
    (pullback.fst it cmp ≫ pullback.fst (g₀ ≫ scalarMorphism s) b)
  change pullback.snd it cmp ≫ pullback.fst C.sourceScalars b ≫ C.originalSourceMap = _
  rw [← fullSourceComparison_fst, ← Category.assoc,
    ← pullback.condition (f := it) (g := cmp), Category.assoc, testFirst_fst]
  simp only [Category.assoc]

/-- Descent retains the original boundary value of the prescribed chart coefficient. -/
theorem fullTestDescend_boundary (hb : ∀ y : Y, b y ∈ C.wholeLocus)
    (t : (invariantSheaf ec).obj.obj (op Wc)) :
    (it).appTop (C.fullTestDescend b hc (C.testBoundaryLift b hb t)).val =
      OriginalScalarSource.originalTestBoundaryValue f hL d V c k W b t := by
  exact C.fullTestDescend_boundary_of_tests b hc it (C.testBoundaryLift b hb t) _
    (C.fullTestCover_boundary b hc hb t)

/-- The descended coefficient has the unchanged original boundary value on the whole test. -/
theorem fullTestBoundary_lift (hb : ∀ y : Y, b y ∈ C.wholeLocus)
    (t : (invariantSheaf ec).obj.obj (op Wc)) :
    ∃ v : OriginalScalarSource.testRing f hL d V c k W b,
      (it).appTop v.val =
        OriginalScalarSource.originalTestBoundaryValue f hL d V c k W b t ∧
      (cmp).appTop v.val = (C.testBoundaryLift b hb t).val :=
  ⟨C.fullTestDescend b hc (C.testBoundaryLift b hb t), C.fullTestDescend_boundary b hc hb t,
    C.fullTestDescend_spec b hc (C.testBoundaryLift b hb t)⟩

end OriginalScalarAffineChart
end FLT.Mazur.HilbertChart.AffineRestriction
