/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFixedBaseRelation
public import FLT.Mazur.VariableHilbertFixedBaseQuotient
public import FLT.Mazur.AffineHilbertRestrictedQuotient

/-!
# Restriction commutes with the original invariant quotient comparison

The constructed map on restricted full relations gives the locally ringed
quotient map. Its square with the original unrestricted quotients commutes,
including regular functions and the coefficient base.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
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
variable {A : Over (Spec (.of R))} {B : Over (Spec (.of R'))}
  (k : A ⟶ variableHilbertTest f d V) (l : B ⟶ variableHilbertTest (Limits.pullback.snd f a) d W)
  (u : (Over.map a).obj B ⟶ A) (hu : u ≫ k = (Over.map a).map l ≫
    variableHilbertFixedBaseProjection f a hL d V W t)

local notation "e" => equivalence f hL d V c k
local notation "e'" => equivalence q h d W c' l
local notation "r" => fixedBaseRelationMap f a hL d V W t c k l u hu

/-- The original restricted invariant quotients are compared by the actual relation map. -/
def fixedBaseQuotientMap :
    invariantLocallyRingedSpace e' ⟶ invariantLocallyRingedSpace e :=
  invariantMap e e' u.left (r).left
    (congrArg Over.Hom.left (fixedBaseRelationMap_fst f a hL d V W t c k l u hu))
    (congrArg Over.Hom.left (fixedBaseRelationMap_snd f a hL d V W t c k l u hu))

/-- The comparison retains the actual original restricted source map. -/
@[reassoc]
theorem fixedBaseQuotientMap_projection :
    invariantLocallyRingedProjection e' ≫ fixedBaseQuotientMap f a hL d V W t c k l u hu =
      u.left.toLRSHom ≫ invariantLocallyRingedProjection e :=
  invariantMap_projection _ _ _ _ _ _

/-- The restricted comparison retains the change of coefficient base. -/
theorem fixedBaseQuotientMap_base :
    fixedBaseQuotientMap f a hL d V W t c k l u hu ≫ invariantLocallyRingedBaseMap e =
      invariantLocallyRingedBaseMap e' ≫ a.toLRSHom :=
  invariantMap_base _ _ _ _ _ _ a (Over.w u)

/-- Restriction and localization commute on the full invariant locally ringed quotients. -/
theorem fixedBaseQuotientMap_restriction :
    fixedBaseQuotientMap f a hL d V W t c k l u hu ≫
        restrictedInvariantQuotientMap f hL d V c k =
      restrictedInvariantQuotientMap q h d W c' l ≫
        variableChartFixedBaseQuotientMap f a hL d V W t c := by
  apply invariantMap_hom_ext e'
  rw [fixedBaseQuotientMap_projection_assoc, restrictedInvariantQuotientMap_projection,
    restrictedInvariantQuotientMap_projection_assoc,
    variableChartFixedBaseQuotientMap_projection,
    ← Scheme.Hom.comp_toLRSHom_assoc, ← Scheme.Hom.comp_toLRSHom_assoc]
  have hh : u.left ≫ k.left = l.left ≫ (P).left := congrArg Over.Hom.left hu
  rw [hh]

/-- The actual inverse image of an original quotient open on the restricted source. -/
theorem fixedBaseQuotientMap_sourceOpen_le (O : TopologicalSpace.Opens (Orbit e)) :
    (pullOpen e' ((TopologicalSpace.Opens.map
      (fixedBaseQuotientMap f a hL d V W t c k l u hu).base).obj O)).val ≤
        u.left ⁻¹ᵁ (pullOpen e O).val :=
  invariantMap_sourceOpen_le _ _ _ _ _ _ O

/-- The constructed sheaf map is the ORIGINAL restricted source pullback. -/
theorem fixedBaseQuotientMap_source_app (O : TopologicalSpace.Opens (Orbit e)) :
    (fixedBaseQuotientMap f a hL d V W t c k l u hu).c.app (op O) ≫
      (invariantInclusion e').hom.app (op ((TopologicalSpace.Opens.map
        (fixedBaseQuotientMap f a hL d V W t c k l u hu).base).obj O)) =
    (invariantInclusion e).hom.app (op O) ≫ u.left.appLE _ _
      (fixedBaseQuotientMap_sourceOpen_le f a hL d V W t c k l u hu O) :=
  invariantMap_source_app _ _ _ _ _ _ O

end FLT.Mazur.HilbertChart.AffineRestriction
