/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertChartInvariantComparison
public import FLT.Mazur.OrderedHilbertIdentityQuotientCover

/-!
# A full original-relation open cover of the old locally ringed quotient

Each selected etale translated chart now uses the entire constructed source
and its entire restricted original relation. Their invariant quotients form
an actual open cover of the old original quotient, with the coefficient
maps preserved. Scheme effectivity of these open neighborhoods remains open.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedHilbertFullChartCover
open HilbertChart CartierAbel SchemePicard FCurve RelativeRelationOrbit
open OrderedHilbertAffineEtaleTestCover OrderedHilbertFaithfulTestCover AffineRestriction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
local notation "T" => smoothHilbertSource f
local notation "s" => smoothHilbertSourceSection f hL
local notation "E" => fun x ↦ Sigma.fst (Sigma.snd (chartData f hL T s x))
local notation "d" => fun x ↦ Prod.snd (Sigma.fst (chartData f hL T s x))
local notation "c" => fun x ↦ chartClass f hL T s x
local notation "e" => smoothHilbertEquivalenceRelation f hL
local notation "e'" => fun x ↦
  OrderedHilbertBaseOpenChart.fullRestrictedEquivalence f hL (d x) (E x) (c x)

/-- Every member is the full invariant quotient of an actual original-source restriction. -/
def chart (x : (T).left) : LocallyRingedSpace := invariantLocallyRingedSpace (e' x)

/-- The actual open inclusion into the old original quotient. -/
def inclusion (x : (T).left) : chart f hL x ⟶ invariantLocallyRingedSpace e :=
  OrderedHilbertBaseOpenChart.fullOriginalQuotientInclusion f hL (d x) (E x) (c x)

instance inclusion_isOpenImmersion (x : (T).left) :
    LocallyRingedSpace.IsOpenImmersion (inclusion f hL x) :=
  OrderedHilbertBaseOpenChart.fullOriginalQuotientInclusion_isOpenImmersion f hL _ _ _

/-- Every member retains its exact original coefficient morphism. -/
theorem inclusion_base (x : (T).left) :
    inclusion f hL x ≫ invariantLocallyRingedBaseMap e = invariantLocallyRingedBaseMap (e' x) :=
  OrderedHilbertBaseOpenChart.fullOriginalQuotientInclusion_base f hL _ _ _

/-- The faithful cover's chosen point survives the full original-relation comparison. -/
theorem point_covers (x : (T).left) : projection e x ∈ Set.range (inclusion f hL x).base := by
  change projection e x ∈ Set.range
    (OrderedHilbertBaseOpenChart.fullOriginalQuotientInclusion f hL (d x) (E x) (c x)).base
  rw [OrderedHilbertBaseOpenChart.fullOriginalQuotientInclusion_range,
    ← smoothTranslationQuotientInclusion_range]
  obtain ⟨y, hy⟩ := OrderedHilbertIdentityQuotientCover.point_covers f hL x
  change (smoothTranslationQuotientInclusion f hL (d x) (E x) (c x)).base
    ((identityGroundOriginalQuotientMap f hL (d x) (E x) (c x)
      (AffineParameterNeighborhood.chart f (d x) (E x) (retainedParameter f hL x))).base y) =
        projection e x at hy
  exact ⟨_, hy⟩

/-- These full original-relation open neighborhoods cover every old original quotient point. -/
theorem covers (z : Orbit e) : ∃ (x : (T).left) (y : chart f hL x),
    (inclusion f hL x).base y = z := by
  obtain ⟨x, rfl⟩ := projection_surjective e z
  obtain ⟨y, hy⟩ := point_covers f hL x
  exact ⟨x, y, hy⟩

/-- The full original-relation neighborhoods form an actual open covering family. -/
theorem ranges_eq_univ : ⋃ x : (T).left, Set.range (inclusion f hL x).base = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  obtain ⟨x, y, hy⟩ := covers f hL z
  exact Set.mem_iUnion.mpr ⟨x, y, hy⟩

end FLT.Mazur.OrderedHilbertFullChartCover
