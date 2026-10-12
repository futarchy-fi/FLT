/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertFixedBaseRelation
public import FLT.Mazur.RelativeRelationInvariantMapSections

/-!
# The original invariant quotient map for localized varying charts

The full-relation comparison descends as a locally ringed morphism, retaining
its original source and coefficient base. This does not assert that either
invariant quotient is a scheme.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open FCurve CartierAbel SchemePicard RelativeRelationOrbit
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
local notation "J" => variableChartRelation q h d W c'

local notation "e" => variableChartEquivalenceRelation f hL d V c
local notation "e'" => variableChartEquivalenceRelation q h d W c'
local notation "r" => variableChartFixedBaseRelationProjection f a hL d V W t c

/-- The actual full relation induces the original invariant locally ringed comparison. -/
def variableChartFixedBaseQuotientMap :
    invariantLocallyRingedSpace e' ⟶ invariantLocallyRingedSpace e :=
  invariantMap e e' (P).left (r).left
    (congrArg Over.Hom.left (variableChartFixedBaseRelationProjection_fst f a hL d V W t c))
    (congrArg Over.Hom.left (variableChartFixedBaseRelationProjection_snd f a hL d V W t c))

/-- The quotient map preserves the full original chart projection. -/
@[reassoc]
theorem variableChartFixedBaseQuotientMap_projection :
    invariantLocallyRingedProjection e' ≫
        variableChartFixedBaseQuotientMap f a hL d V W t c =
      (P).left.toLRSHom ≫ invariantLocallyRingedProjection e :=
  invariantMap_projection _ _ _ _ _ _

/-- The quotient comparison retains the original coefficient base morphism. -/
theorem variableChartFixedBaseQuotientMap_base :
    variableChartFixedBaseQuotientMap f a hL d V W t c ≫ invariantLocallyRingedBaseMap e =
      invariantLocallyRingedBaseMap e' ≫ a.toLRSHom :=
  invariantMap_base _ _ _ _ _ _ a (Over.w P)

/-- Every local chart point maps to its original orbit. -/
theorem variableChartFixedBaseQuotientMap_apply (x : (variableHilbertTest q d W).left) :
    (variableChartFixedBaseQuotientMap f a hL d V W t c).base (projection e' x) =
      projection e ((P).left x) := invariantMap_projection_apply _ _ _ _ _ _ x

end FLT.Mazur.HilbertChart
