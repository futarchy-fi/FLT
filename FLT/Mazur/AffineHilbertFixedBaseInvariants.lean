/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFixedBaseRelation
public import FLT.Mazur.SchemeRelationInvariantFunctorial

/-!
# Full invariant models across changed Picard translations and ground bases

The actual full-relation map induces a comparison of newly computed invariant
models. This preserves original functions and both endpoint equations without
identifying the new model with a pullback of the old one.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open FCurve CartierAbel SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R R' : Type} [CommRing R] [CommRing R']
  [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ R']
  {X : Scheme} (f : X ⟶ Spec (.of R)) (a : Spec (.of R') ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {L : X.Modules} (hL : AmpleLineBundle L) (d : ℕ)
  (V : Over (Spec (.of R))) (W : Over (Spec (.of R')))
  (t : (Over.map a).obj W ⟶ V) (c : (relativeFppfSheaf f).obj.obj (op V))
local notation "q" => Limits.pullback.snd f a
local instance : SmoothOfRelativeDimension 1 q :=
  MorphismProperty.pullback_snd _ _ inferInstance
local notation "h" => fixedBaseAmple f a hL
local notation "c'" => fixedBaseTranslationClass f a V W t c
local notation "P" => variableHilbertFixedBaseProjection f a hL d V W t
variable {A : Over (Spec (.of R))} {B : Over (Spec (.of R'))}
  (k : A ⟶ variableHilbertTest f d V) (l : B ⟶ variableHilbertTest (Limits.pullback.snd f a) d W)
  (u : (Over.map a).obj B ⟶ A) (hu : u ≫ k = (Over.map a).map l ≫
    variableHilbertFixedBaseProjection f a hL d V W t)

local notation "p₀" => Over.Hom.left (fst f hL d V c k)
local notation "q₀" => Over.Hom.left (snd f hL d V c k)
local notation "p₁" => Over.Hom.left (fst q h d W c' l)
local notation "q₁" => Over.Hom.left (snd q h d W c' l)
local notation "v" => Over.Hom.left (fixedBaseRelationMap f a hL d V W t c k l u hu)
local notation "hp" => congrArg Over.Hom.left
  (fixedBaseRelationMap_fst f a hL d V W t c k l u hu)
local notation "hq" => congrArg Over.Hom.left
  (fixedBaseRelationMap_snd f a hL d V W t c k l u hu)

/-- Original full invariants pull back to full invariants of the genuinely changed chart. -/
def fixedBaseInvariantPullback :
    SchemeEffectiveEpiSections.compatibleFunctions p₀ q₀ →+*
      SchemeEffectiveEpiSections.compatibleFunctions p₁ q₁ :=
  SchemeRelationInvariantSpectrum.relationPullback p₀ q₀ p₁ q₁ u.left v hp hq

/-- The coefficient comparison is the actual original source pullback. -/
theorem fixedBaseInvariantPullback_val
    (s : SchemeEffectiveEpiSections.compatibleFunctions p₀ q₀) :
    (fixedBaseInvariantPullback f a hL d V W t c k l u hu s).val = u.left.appTop s.val := rfl

/-- The newly computed invariant target maps to the old target as an actual scheme. -/
def fixedBaseInvariantTargetMap :
    SchemeRelationInvariantSpectrum.target p₁ q₁ ⟶
      SchemeRelationInvariantSpectrum.target p₀ q₀ :=
  SchemeRelationInvariantSpectrum.relationMap p₀ q₀ p₁ q₁ u.left v hp hq

/-- The complete changed source square commutes, including the structure-sheaf maps. -/
@[reassoc]
theorem fixedBaseInvariantTargetMap_projection :
    SchemeRelationInvariantSpectrum.projection p₁ q₁ ≫
      fixedBaseInvariantTargetMap f a hL d V W t c k l u hu =
        u.left ≫ SchemeRelationInvariantSpectrum.projection p₀ q₀ :=
  SchemeRelationInvariantSpectrum.projection_relationMap p₀ q₀ p₁ q₁ u.left v hp hq

end FLT.Mazur.HilbertChart.AffineRestriction
