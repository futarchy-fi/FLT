/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFixedBaseRelationInverse
public import FLT.Mazur.AffineHilbertFixedBaseQuotient
public import FLT.Mazur.RelativeRelationInvariantIso

/-!
# Restricted invariant quotient isomorphisms under monic base localization

The actual inverse full relation proves that the previously constructed
quotient comparison is an isomorphism of locally ringed spaces.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open FCurve CartierAbel SchemePicard RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R R' : Type} [CommRing R] [CommRing R']
  [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ R']
  {X : Scheme} (f : X ⟶ Spec (.of R)) (a : Spec (.of R') ⟶ Spec (.of R)) [Mono a]
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
    variableHilbertFixedBaseProjection f a hL d V W t) [IsIso u]

local notation "e" => equivalence f hL d V c k
local notation "e'" => equivalence q h d W c' l
local notation "r" => fixedBaseRelationMap f a hL d V W t c k l u hu

/-- The full inverse relation gives the original restricted invariant quotient isomorphism. -/
def fixedBaseQuotientIso :
    invariantLocallyRingedSpace e' ≅ invariantLocallyRingedSpace e :=
  invariantIso e e' ((Over.forget _).mapIso (asIso u))
    ((Over.forget _).mapIso (fixedBaseRelationIso f a hL d V W t c k l u hu))
    (congrArg Over.Hom.left (fixedBaseRelationMap_fst f a hL d V W t c k l u hu))
    (congrArg Over.Hom.left (fixedBaseRelationMap_snd f a hL d V W t c k l u hu))

/-- The forward isomorphism is exactly the existing original quotient comparison. -/
theorem fixedBaseQuotientIso_hom : (fixedBaseQuotientIso f a hL d V W t c k l u hu).hom =
    fixedBaseQuotientMap f a hL d V W t c k l u hu := rfl

/-- The original quotient map is now proved invertible, including its invariant sheaf map. -/
instance fixedBaseQuotientMap_isIso :
    IsIso (fixedBaseQuotientMap f a hL d V W t c k l u hu) := by
  rw [← fixedBaseQuotientIso_hom f a hL d V W t c k l u hu]
  infer_instance

/-- The inverse quotient map retains the inverse original source morphism. -/
@[reassoc]
theorem fixedBaseQuotientIso_inv_projection :
    invariantLocallyRingedProjection e ≫ (fixedBaseQuotientIso f a hL d V W t c k l u hu).inv =
      (inv u).left.toLRSHom ≫ invariantLocallyRingedProjection e' :=
by
  apply (cancel_mono (fixedBaseQuotientIso f a hL d V W t c k l u hu).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    fixedBaseQuotientIso_hom, fixedBaseQuotientMap_projection,
    ← Scheme.Hom.comp_toLRSHom_assoc]
  have hh : (inv u).left ≫ u.left = 𝟙 _ :=
    congrArg Over.Hom.left (IsIso.inv_hom_id u)
  rw [hh]
  exact (Category.id_comp _).symm

end FLT.Mazur.HilbertChart.AffineRestriction
