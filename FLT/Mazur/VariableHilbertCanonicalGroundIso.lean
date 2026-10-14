/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertGroundBaseCartesian
public import FLT.Mazur.RelativeCoefficientBaseChange

/-!
# Actual Hilbert parameters for the canonical changed translation

Pull back the entire old translation scheme. The freshly constructed Hilbert
parameter scheme is then canonically isomorphic to the actual ground pullback
of the original parameter scheme, including its structure sheaf.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open FCurve CartierAbel SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R R' : Type} [CommRing R] [CommRing R']
  [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ R']
  {X : Scheme} (f : X ⟶ Spec (.of R)) (a : Spec (.of R') ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {L : X.Modules} (hL : AmpleLineBundle L) (d : ℕ) (V : Over (Spec (.of R)))
local notation "q" => Limits.pullback.snd f a
local instance canonicalGroundSmooth : SmoothOfRelativeDimension 1 q :=
  MorphismProperty.pullback_snd _ _ inferInstance
local notation "W" => RelativeCoefficientBaseChange.target a (T := V)
local notation "t" => RelativeCoefficientBaseChange.toOld a (T := V)
local notation "P" => variableHilbertFixedBaseProjection f a hL d V W t

/-- The full canonical translation change makes the Hilbert square Cartesian over the ground. -/
theorem variableHilbertCanonicalGround_isPullback :
    IsPullback (P).left (variableHilbertTest q d W).hom (variableHilbertTest f d V).hom a := by
  have h := (variableHilbertGroundBase_isPullback f a hL d V W t).paste_vert
    (IsPullback.of_hasPullback V.hom a)
  change IsPullback (P).left ((variableHilbertBase q d W).left ≫ (W).hom)
    ((variableHilbertBase f d V).left ≫ V.hom) a at h
  simpa only [Over.w] using h

/-- An actual scheme isomorphism to the complete ground-changed parameter space. -/
def variableHilbertCanonicalGroundIso :
    (variableHilbertTest q d W).left ≅ pullback (variableHilbertTest f d V).hom a :=
  (variableHilbertCanonicalGround_isPullback f a hL d V).isoPullback

@[reassoc]
theorem variableHilbertCanonicalGroundIso_old :
    (variableHilbertCanonicalGroundIso f a hL d V).inv ≫ (P).left =
      pullback.fst (variableHilbertTest f d V).hom a :=
  (variableHilbertCanonicalGround_isPullback f a hL d V).isoPullback_inv_fst

@[reassoc]
theorem variableHilbertCanonicalGroundIso_new :
    (variableHilbertCanonicalGroundIso f a hL d V).inv ≫ (variableHilbertTest q d W).hom =
      pullback.snd (variableHilbertTest f d V).hom a :=
  (variableHilbertCanonicalGround_isPullback f a hL d V).isoPullback_inv_snd

end FLT.Mazur.HilbertChart
