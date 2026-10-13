/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertIdentityGroundQuotientChart
public import FLT.Mazur.VariableHilbertFixedBaseQuotient

/-!
# Constructed affine sources mapping to the original quotient

Compose the effective refined quotient chart with the actual ground-base
quotient comparison. This produces a morphism of locally ringed spaces to
the old quotient and retains every old restricted orbit. Openness or descent
of this comparison is not inferred from its surjectivity on these points.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left] (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left]
local instance : Algebra.FiniteType ℤ Γ(V.left, ⊤) :=
  AffineEtaleIdentityGroundBase.coefficient_finiteType V
local notation "a" => AffineEtaleIdentityGroundBase.base V
local notation "W" => AffineEtaleIdentityGroundBase.translation V
local notation "t" => AffineEtaleIdentityGroundBase.comparison V
local notation "q" => Limits.pullback.snd f a
local instance : SmoothOfRelativeDimension 1 q :=
  MorphismProperty.pullback_snd _ _ inferInstance
local notation "u" => groundBaseSourceMap f a hL d V W t k
local notation "l" => groundBaseSourceChart f a hL d V W t k
local notation "h'" => fixedBaseAmple f a hL
local notation "c'" => fixedBaseTranslationClass f a V W t c
local notation "e" => variableChartEquivalenceRelation f hL d V c

/-- The affine refined quotient maps to the original unrestricted invariant quotient. -/
def identityGroundOriginalQuotientMap :
    (fullEnvelopeScheme q h' d W c' l).toLocallyRingedSpace ⟶ invariantLocallyRingedSpace e :=
  fullEnvelopeOpenChart q h' d W c' l ≫ variableChartFixedBaseQuotientMap f a hL d V W t c

/-- The comparison remembers the actual original parameter point. -/
theorem identityGroundOriginalQuotientMap_projection
    (y : (groundBaseSource f a hL d V W t k).left) :
    (identityGroundOriginalQuotientMap f hL d V c k).base
      (fullEnvelopeProjection q h' d W c' l y) = projection e (k.left ((u).left y)) := by
  change (variableChartFixedBaseQuotientMap f a hL d V W t c).base
    ((fullEnvelopeOpenChart q h' d W c' l).base
      (fullEnvelopeProjection q h' d W c' l y)) = _
  rw [fullEnvelopeOpenChart_projection, variableChartFixedBaseQuotientMap_apply]
  apply congrArg (projection e)
  exact (congrArg (fun g ↦ g.left y) (groundBaseSource_square f a hL d V W t k)).symm

/-- Every original restricted orbit belongs to the image of this constructed affine scheme. -/
theorem identityGroundOriginalQuotientMap_contains (x : A.left) :
    projection e (k.left x) ∈ Set.range (identityGroundOriginalQuotientMap f hL d V c k).base := by
  obtain ⟨y, hy⟩ := (u).left.surjective x
  refine ⟨fullEnvelopeProjection q h' d W c' l y, ?_⟩
  rw [identityGroundOriginalQuotientMap_projection, hy]

end FLT.Mazur.HilbertChart.AffineRestriction
