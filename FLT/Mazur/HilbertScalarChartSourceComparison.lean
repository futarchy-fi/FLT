/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOriginalScalarTestAtlas
public import FLT.Mazur.SchemeScalarSourceComparison

/-!
# Comparing the actual Hilbert scalar chart with the whole source

The chart's scalar map is the unchanged original source map followed by its
invariant scalar morphism. Its test comparison is cartesian and its exact
image is the inverse image of the original chart image.
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

omit [Etale V.hom] in
/-- The actual scalar chart map factors through the unchanged original source. -/
theorem sourceScalars_original : C.sourceScalars = C.originalSourceMap ≫ scalarMorphism s := by
  rw [sourceScalars, ← scalarMorphism_through_quotient,
    normalizedSource_scalarMorphism_factor]
  rfl

open SchemeScalarRelationPullback
variable {Y : Scheme} (b : Y ⟶ Spec (.of
  ((invariantSheaf (equivalence f hL d V c k)).obj.obj (op W))))

/-- The actual comparison from the chosen Hilbert chart test to the whole source test. -/
def fullSourceComparison : testSource C.sourceScalars b ⟶ testSource (scalarMorphism s) b :=
  (IsPullback.of_hasPullback (scalarMorphism s) b).flip.lift
    (pullback.snd C.sourceScalars b)
    (pullback.fst C.sourceScalars b ≫ C.originalSourceMap) (by
      rw [Category.assoc, ← C.sourceScalars_original, pullback.condition])

omit [Etale V.hom] in
@[simp, reassoc]
theorem fullSourceComparison_fst :
    C.fullSourceComparison b ≫ pullback.fst (scalarMorphism s) b =
      pullback.fst C.sourceScalars b ≫ C.originalSourceMap :=
  (IsPullback.of_hasPullback (scalarMorphism s) b).flip.lift_snd _ _ _

omit [Etale V.hom] in
@[simp, reassoc]
theorem fullSourceComparison_snd :
    C.fullSourceComparison b ≫ pullback.snd (scalarMorphism s) b =
      pullback.snd C.sourceScalars b :=
  (IsPullback.of_hasPullback (scalarMorphism s) b).flip.lift_fst _ _ _

omit [Etale V.hom] in
/-- The actual chosen chart comparison is base change of its original source map. -/
theorem fullSourceComparison_isPullback : IsPullback (C.fullSourceComparison b)
    (pullback.fst C.sourceScalars b) (pullback.fst (scalarMorphism s) b)
      C.originalSourceMap := by
  have h : IsPullback (pullback.snd C.sourceScalars b) (pullback.fst C.sourceScalars b)
      b (C.originalSourceMap ≫ scalarMorphism s) := by
    rw [← C.sourceScalars_original]
    exact (IsPullback.of_hasPullback C.sourceScalars b).flip
  exact h.of_right' (IsPullback.of_hasPullback (scalarMorphism s) b).flip

/-- Original chart etaleness survives the comparison of actual scalar-test sources. -/
instance fullSourceComparisonEtale : Etale (C.fullSourceComparison b) :=
  MorphismProperty.of_isPullback (C.fullSourceComparison_isPullback b).flip inferInstance

attribute [local irreducible] fullSourceComparison

omit [Etale V.hom] in
/-- The comparison covers precisely the original chart image on the full scalar source. -/
theorem fullSourceComparison_range : Set.range (C.fullSourceComparison b) =
    pullback.fst (scalarMorphism s) b ⁻¹' Set.range C.originalSourceMap := by
  have h := Scheme.image_preimage_eq_of_isPullback
    (C.fullSourceComparison_isPullback b).flip Set.univ
  simp only [Set.preimage_univ, Set.image_univ] at h
  convert h using 1
  ext x
  rfl

/-- The exact remaining geometric coverage condition supplies an actual singleton cover. -/
theorem fullSourceComparison_covers
    (hc : ∀ x : testSource (scalarMorphism s) b,
      pullback.fst (scalarMorphism s) b x ∈ Set.range C.originalSourceMap) :
    Presieve.singleton (C.fullSourceComparison b) ∈
      Scheme.fppfPrecoverage (testSource (scalarMorphism s) b) := by
  let _ : Surjective (C.fullSourceComparison b) := ⟨by
    rw [← Set.range_eq_univ, C.fullSourceComparison_range b, Set.eq_univ_iff_forall]
    exact hc⟩
  exact Scheme.Hom.singleton_mem_fppfPrecoverage _

end OriginalScalarAffineChart
end FLT.Mazur.HilbertChart.AffineRestriction
