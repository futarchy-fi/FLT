/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineEtaleIdentityGroundBase
public import FLT.Mazur.AffineHilbertGroundBaseSource
public import FLT.Mazur.HilbertSubterminalTranslationEnvelope

/-!
# Initial full fibers over the translation coefficient spectrum

Every open affine Hilbert parameter source has a ground refinement with full
fibers at every point. Its source comparison is an actual scheme isomorphism.
The old unrestricted envelope is not asserted to be full: the independent
translation now lives over the changed coefficient spectrum.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
local instance identityGroundCoefficients : Algebra.FiniteType ℤ Γ(V.left, ⊤) :=
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

/-- The source is unchanged up to an actual scheme isomorphism. -/
instance identityGroundSourceMap_isIso : IsIso (u).left :=
  (groundBaseSource_isPullback f a hL d V W t k).isIso_fst_of_isIso

variable [IsOpenImmersion k.left]

/-- Reflexivity fills the ORIGINAL complete relation for the new coefficient family. -/
instance identityGroundEnvelope_isIso : IsIso (toEnvelope q h' d W c' l).left :=
  subterminal_toEnvelope_isIso q h' d W c' l

/-- Every point of this constructed refinement belongs to its full-fiber interior. -/
theorem identityGround_fullInterior : fullEnvelopeInterior q h' d W c' l = ⊤ :=
  subterminal_fullEnvelopeInterior q h' d W c' l

/-- Each original point survives in a full-fiber interior; fullness is constructed, not assumed. -/
theorem exists_identityGround_fullInterior (x : A.left) :
    ∃ y : (B).left, (u).left y = x ∧ y ∈ fullEnvelopeInterior q h' d W c' l := by
  obtain ⟨y, hy⟩ := (u).left.surjective x
  exact ⟨y, hy, by rw [identityGround_fullInterior]; trivial⟩

end FLT.Mazur.HilbertChart.AffineRestriction
