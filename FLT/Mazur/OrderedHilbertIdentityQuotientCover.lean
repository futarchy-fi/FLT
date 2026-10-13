/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertAffineParameterNeighborhood
public import FLT.Mazur.HilbertIdentityGroundSourceIso
public import FLT.Mazur.OrderedHilbertFaithfulParameterPoint

/-!
# Constructed affine scheme sources covering the original invariant quotient

Retain the faithful cover's chosen original parameter, restrict the parameter
scheme affinely, and construct the full-fiber identity ground refinement.
Its effective affine quotient maps to the original invariant quotient and
these actual maps cover every original orbit. They are topologically open;
global scheme descent is a separate construction.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedHilbertIdentityQuotientCover
open HilbertChart CartierAbel SchemePicard FCurve RelativeRelationOrbit
open OrderedHilbertAffineEtaleTestCover OrderedHilbertFaithfulTestCover AffineRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
local notation "T" => smoothHilbertSource f
local notation "s" => smoothHilbertSourceSection f hL
local notation "E" => fun x ↦ Sigma.fst (Sigma.snd (chartData f hL T s x))
local notation "d" => fun x ↦ Prod.snd (Sigma.fst (chartData f hL T s x))
local notation "c" => fun x ↦ chartClass f hL T s x
local notation "p" => fun x ↦ retainedParameter f hL x
local notation "k" => fun x ↦ AffineParameterNeighborhood.chart f (d x) (E x) (p x)
local instance (x : (smoothHilbertSource f).left) : Algebra.FiniteType ℤ Γ((E x).left, ⊤) :=
  AffineEtaleIdentityGroundBase.coefficient_finiteType (E x)
local notation "a" => fun x ↦ AffineEtaleIdentityGroundBase.base (E x)
local notation "W" => fun x ↦ AffineEtaleIdentityGroundBase.translation (E x)
local notation "t" => fun x ↦ AffineEtaleIdentityGroundBase.comparison (E x)
local notation "q" => fun x ↦ Limits.pullback.snd f (a x)
local instance (x : (smoothHilbertSource f).left) : SmoothOfRelativeDimension 1 (q x) :=
  MorphismProperty.pullback_snd _ _ inferInstance
local notation "h" => fun x ↦ fixedBaseAmple f (a x) hL
local notation "c'" => fun x ↦ fixedBaseTranslationClass f (a x) (E x) (W x) (t x) (c x)
local notation "l" => fun x ↦ groundBaseSourceChart f (a x) hL (d x) (E x) (W x) (t x) (k x)

/-- The effective quotient of the constructed full-envelope affine ground refinement. -/
def source (x : (smoothHilbertSource f).left) : Scheme :=
  fullEnvelopeScheme (q x) (h x) (d x) (W x) (c' x) (l x)

instance source_affine (x : (smoothHilbertSource f).left) : IsAffine (source f hL x) :=
  fullEnvelopeTarget_affine (q x) (h x) (d x) (W x) (c' x) (l x)

/-- The actual locally ringed morphism to the ORIGINAL global invariant quotient. -/
def toOriginal (x : (smoothHilbertSource f).left) :
    (source f hL x).toLocallyRingedSpace ⟶
      invariantLocallyRingedSpace (smoothHilbertEquivalenceRelation f hL) :=
  identityGroundOriginalQuotientMap f hL (d x) (E x) (c x) (k x) ≫
    smoothTranslationQuotientInclusion f hL (d x) (E x) (c x)

/-- Each covering morphism is open on the underlying original orbit space. -/
theorem toOriginal_isOpenMap (x : (smoothHilbertSource f).left) :
    IsOpenMap (toOriginal f hL x).base := by
  have hj : LocallyRingedSpace.IsOpenImmersion
      (smoothTranslationQuotientInclusion f hL (d x) (E x) (c x)) := inferInstance
  exact hj.base_open.isOpenMap.comp
    (identityGroundOriginalQuotientMap_isOpenMap f hL (d x) (E x) (c x) (k x))

/-- The original faithful cover's retained point survives all subsequent refinements. -/
theorem point_covers (x : (smoothHilbertSource f).left) :
    projection (smoothHilbertEquivalenceRelation f hL) x ∈ Set.range (toOriginal f hL x).base := by
  obtain ⟨y, hy⟩ := identityGroundOriginalQuotientMap_contains f hL (d x) (E x) (c x) (k x)
    (AffineParameterNeighborhood.point f (d x) (E x) (p x))
  rw [AffineParameterNeighborhood.point_chart] at hy
  refine ⟨y, ?_⟩
  change (smoothTranslationQuotientInclusion f hL (d x) (E x) (c x)).base
    ((identityGroundOriginalQuotientMap f hL (d x) (E x) (c x) (k x)).base y) = _
  rw [hy, retainedParameter_quotient]

/-- Every point of the original quotient is covered by a constructed affine scheme source. -/
theorem covers (z : Orbit (smoothHilbertEquivalenceRelation f hL)) :
    ∃ (x : (smoothHilbertSource f).left) (y : source f hL x),
      (toOriginal f hL x).base y = z := by
  obtain ⟨x, rfl⟩ := projection_surjective (smoothHilbertEquivalenceRelation f hL) z
  obtain ⟨y, hy⟩ := point_covers f hL x
  exact ⟨x, y, hy⟩

/-- The ranges of these specific effective affine sources cover the entire original orbit space. -/
theorem ranges_eq_univ :
    ⋃ x : (smoothHilbertSource f).left, Set.range (toOriginal f hL x).base = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  obtain ⟨x, y, hy⟩ := covers f hL z
  exact Set.mem_iUnion.mpr ⟨x, y, hy⟩

end FLT.Mazur.OrderedHilbertIdentityQuotientCover
