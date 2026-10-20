/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertScalarChartBoundaryTests

/-!
# Actual correction-atlas refinements of the scalar-test charts

Pull the existing finite correction atlas back to the constructed scalar-test
source. It is still a finite fppf cover. The difference between each old lift
and the new full test-invariant lift is an actual original-boundary kernel
correction. The corrected family satisfies the full pulled relation equations.
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
  originalBoundarySource originalBoundarySourceMap originalClosedRelation
  originalClosedFst originalClosedSnd originalClosedArrow InvariantBoundary.boundary
  normalizedOriginalBoundaryInclusion normalizedOriginalBoundaryAction
  normalizedOriginalScalarMap

namespace OriginalScalarAffineChart
variable {f hL d V c k W} (C : OriginalScalarAffineChart f hL d V c k W)
local notation "ρ" => restrictedAction
  (normalizedFullRelationAction f hL d V c k C.size C.label) C.domain C.stable
local notation "σ" => normalizedOriginalScalarMap f hL d V c k C.size C.label W
  C.domain C.stable C.overDomain
local notation "j" => C.domain.ι ≫ normalizedFullRelationFirst f hL d V c k C.size C.label

open SchemeScalarRelationPullback OrbitBoundaryAtlas
open OrbitBoundaryAtlas.FiniteAtlas
attribute [local irreducible] OrbitBoundaryAtlas.finiteCharts
  OrbitBoundaryAtlas.FiniteAtlas.lifts
  OriginalScalarAffineChart.testBoundaryLift OriginalScalarAffineChart.testBoundaryValue
variable (hW : IsAffineOpen (pullOpen (equivalence f hL d V c k) W).val)
  {Y : Scheme} (b : Y ⟶ Spec (.of
    ((invariantSheaf (equivalence f hL d V c k)).obj.obj (op W))))
local notation "Old" => finiteCharts f hL d V c k W hW
local notation "oldMap" a:max => OrbitBoundaryAtlas.chartMap f hL d V c k W (a).val
local notation "Ec" => (pullOpen ec Wc).val
local notation "i" => originalBoundarySourceMap f hL d V c k
local notation "z" => originalClosedArrow f hL d V c k
local notation "g₀" => (openSourceMap eo ec i z
  (originalClosedArrow_fst f hL d V c k) (originalClosedArrow_snd f hL d V c k) W).left
open InvariantOpenRelationDiagram
attribute [local irreducible] RelativeRelationOrbit.openSourceMap
  InvariantOpenRelationDiagram.orbitFunctions

/-- The actual old correction atlas pulled back to the whole scalar-test source. -/
abbrev correctionRefinement : (testSource C.sourceScalars b).Cover Scheme.fppfPrecoverage :=
  (finiteFppfCover f hL d V c k W hW).pullback₁ (C.testOriginalMap b)

/-- The comparison retains the finite index set of the existing correction atlas. -/
instance correctionRefinementFintype : Fintype (C.correctionRefinement hW b).I₀ :=
  inferInstanceAs (Fintype (finiteFppfCover f hL d V c k W hW).I₀)

local notation "r₁" a:max => pullback.fst (C.testOriginalMap b) (oldMap a)
local notation "r₂" a:max => pullback.snd (C.testOriginalMap b) (oldMap a)
local notation "r₀" a:max => r₁ a ≫ C.testOriginalMap b
local notation "i₀" a:max => pullback.fst (r₀ a) g₀
local notation "u" t:max a:max => (OrbitBoundaryAtlas.FiniteAtlas.lifts f hL d V c k W hW t a).val

/-- The new coefficient on each actual member of the old-atlas refinement. -/
def refinementLift (hb : ∀ y : Y, b y ∈ C.wholeLocus)
    (t : (invariantSheaf ec).obj.obj (op Wc)) (a : Old) :
    Γ(pullback (C.testOriginalMap b) (oldMap a), ⊤) :=
  (r₁ a).appTop (C.testBoundaryLift b hb t).val

/-- An explicit correction of the old ambient lift on its actual scalar-chart refinement. -/
def refinementCorrection (hb : ∀ y : Y, b y ∈ C.wholeLocus)
    (t : (invariantSheaf ec).obj.obj (op Wc)) (a : Old) :
    Γ(pullback (C.testOriginalMap b) (oldMap a), ⊤) :=
  (r₂ a).appTop (u t a) - C.refinementLift hW b hb t a

attribute [local irreducible] refinementLift refinementCorrection
  relativeFppfSheaf AmpleLineBundle OrbitBoundaryAtlas.chartMap

/-- The old atlas coefficient has the prescribed value on the refined original boundary. -/
theorem refinement_old_boundary (t : (invariantSheaf ec).obj.obj (op Wc)) (a : Old) :
    (i₀ a).appTop ((r₂ a).appTop (u t a)) =
      (pullback.snd (r₀ a) g₀).appTop (orbitFunctions ec Wc t).val := by
  have ho : (i₀ a) ≫ r₂ a ≫ oldMap a = pullback.snd (r₀ a) g₀ ≫ g₀ := by
    rw [← pullback.condition (f := C.testOriginalMap b) (g := oldMap a)]
    exact pullback.condition (f := r₀ a) (g := g₀)
  exact OrbitBoundaryAtlas.FiniteAtlas.boundary_chart_test f hL d V c k W hW t
    (OrbitBoundaryAtlas.FiniteAtlas.lifts f hL d V c k W hW t) a
    (OrbitBoundaryAtlas.FiniteAtlas.lifts_restrict f hL d V c k W hW t a)
    ((i₀ a) ≫ r₂ a) (pullback.snd (r₀ a) g₀)
    (by simpa only [Category.assoc] using ho)

/-- The new full test-invariant coefficient has that same original boundary value. -/
theorem refinement_new_boundary (hb : ∀ y : Y, b y ∈ C.wholeLocus)
    (t : (invariantSheaf ec).obj.obj (op Wc)) (a : Old) :
    (i₀ a).appTop ((r₁ a).appTop (C.testBoundaryLift b hb t).val) =
      (pullback.snd (r₀ a) g₀).appTop (orbitFunctions ec Wc t).val := by
  apply C.testBoundaryLift_original_test b hb t ((i₀ a) ≫ r₁ a)
    (pullback.snd (r₀ a) g₀)
  rw [Category.assoc]
  exact pullback.condition (f := r₀ a) (g := g₀)

/-- The constructed correction is zero on the entire original boundary pullback. -/
theorem refinementCorrection_boundary (hb : ∀ y : Y, b y ∈ C.wholeLocus)
    (t : (invariantSheaf ec).obj.obj (op Wc)) (a : Old) :
    (i₀ a).appTop (C.refinementCorrection hW b hb t a) = 0 := by
  unfold refinementCorrection refinementLift
  exact (map_sub (i₀ a).appTop.hom _ _).trans (sub_eq_zero.mpr
    ((C.refinement_old_boundary hW b t a).trans (C.refinement_new_boundary hW b hb t a).symm))

/-- Subtracting this genuine boundary-kernel correction recovers the constructed coefficient. -/
theorem refinement_corrected (hb : ∀ y : Y, b y ∈ C.wholeLocus)
    (t : (invariantSheaf ec).obj.obj (op Wc)) (a : Old) :
    (r₂ a).appTop (u t a) - C.refinementCorrection hW b hb t a =
      C.refinementLift hW b hb t a := by
  unfold refinementCorrection
  exact sub_sub_cancel _ _

/-- The corrected old-chart coefficients satisfy every full pulled-relation test. -/
theorem refinement_corrected_relation (hb : ∀ y : Y, b y ∈ C.wholeLocus)
    (t : (invariantSheaf ec).obj.obj (op Wc)) (a a' : Old)
    {Z : Scheme} (v : Z ⟶ pullback (C.testOriginalMap b) (oldMap a))
    (v' : Z ⟶ pullback (C.testOriginalMap b) (oldMap a'))
    (w : Z ⟶ testRelation C.fullFirst C.sourceScalars b)
    (hv : v ≫ r₁ a = w ≫ testFirst C.fullFirst C.sourceScalars b)
    (hv' : v' ≫ r₁ a' = w ≫
      testSecond C.fullFirst C.fullSecond C.sourceScalars C.full_scalar_square b) :
    v.appTop ((r₂ a).appTop (u t a) - C.refinementCorrection hW b hb t a) =
      v'.appTop ((r₂ a').appTop (u t a') - C.refinementCorrection hW b hb t a') := by
  rw [refinement_corrected, refinement_corrected]
  unfold refinementLift
  simp only [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, hv, hv']
  have h := (C.testBoundaryLift b hb t).property
  change (testFirst C.fullFirst C.sourceScalars b).appTop _ =
    (testSecond C.fullFirst C.fullSecond C.sourceScalars C.full_scalar_square b).appTop _ at h
  exact congrArg (fun x ↦ w.appTop x) h

end OriginalScalarAffineChart
end FLT.Mazur.HilbertChart.AffineRestriction
