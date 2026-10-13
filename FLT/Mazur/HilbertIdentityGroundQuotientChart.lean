/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertIdentityGroundBase
public import FLT.Mazur.AffineHilbertEnvelopeOpenChart

/-!
# Affine quotient charts with no initial full-fiber hypothesis

The identity ground refinement constructs fullness at every point of the old
affine open parameter. Its original full relation gives an affine scheme chart
of the refined invariant quotient. The old point is retained by an isomorphism.
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
local notation "B" => groundBaseSource f a hL d V W t k
local notation "u" => groundBaseSourceMap f a hL d V W t k
local notation "l" => groundBaseSourceChart f a hL d V W t k
local notation "h'" => fixedBaseAmple f a hL
local notation "c'" => fixedBaseTranslationClass f a V W t c
local notation "e" => variableChartEquivalenceRelation q h' d W c'

/-- An arbitrary original affine chart point has a constructed affine refined quotient chart. -/
theorem exists_identityGround_quotient_chart (x : A.left) :
    ∃ y : (B).left, (u).left y = x ∧
      y ∈ fullEnvelopeInterior q h' d W c' l ∧
      ∃ (Q : Scheme) (j : Q.toLocallyRingedSpace ⟶ invariantLocallyRingedSpace e),
        IsAffine Q ∧ LocallyRingedSpace.IsOpenImmersion j ∧
          projection e ((l).left y) ∈ Set.range j.base := by
  obtain ⟨y, hy, hfull⟩ := exists_identityGround_fullInterior f hL d V c k x
  refine ⟨y, hy, hfull, fullEnvelopeScheme q h' d W c' l,
    fullEnvelopeOpenChart q h' d W c' l, ?_, inferInstance, ?_⟩
  · exact fullEnvelopeTarget_affine q h' d W c' l
  · exact ⟨fullEnvelopeProjection q h' d W c' l y,
      fullEnvelopeOpenChart_projection q h' d W c' l y⟩

end FLT.Mazur.HilbertChart.AffineRestriction
