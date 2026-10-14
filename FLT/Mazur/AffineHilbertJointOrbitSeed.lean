/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertJointSourceBranch
public import FLT.Mazur.SchemeRelationSeedOrbit

/-!
# Joint Picard effectivity from original source orbit seeds

The seed is monic over the actual joint coefficient model. Meeting every
original source orbit over its generic point constructs whole kernel point
coverage and hence a represented original source, retaining both coefficient
maps of the actual reselection.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.HilbertChart.AffineRestriction
set_option backward.isDefEq.respectTransparency false
open FCurve CartierAbel SchemePicard
attribute [local irreducible] relation fst snd
variable {R R' : Type} [CommRing R] [CommRing R']
  [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ R']
  {X : Scheme} (f : X ⟶ Spec (.of R)) (a : Spec (.of R') ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {L : X.Modules} (hL : AmpleLineBundle L) (d : ℕ)
  (V : Over (Spec (.of R))) (W : Over (Spec (.of R')))
  (t : (Over.map a).obj W ⟶ V) (c : (relativeFppfSheaf f).obj.obj (op V))
local notation "q" => Limits.pullback.snd f a
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
local instance jointOrbitSeedSmooth : SmoothOfRelativeDimension 1 q :=
  MorphismProperty.pullback_snd _ _ inferInstance
local notation "h" => fixedBaseAmple f a hL
local notation "c'" => fixedBaseTranslationClass f a V W t c
local notation "P" => variableHilbertFixedBaseProjection f a hL d V W t
variable {A : Over (Spec (.of R))} {B : Over (Spec (.of R'))}
  (k : A ⟶ variableHilbertTest f d V) (l : B ⟶ variableHilbertTest (Limits.pullback.snd f a) d W)
  (u : (Over.map a).obj B ⟶ A) (hu : u ≫ k = (Over.map a).map l ≫
    variableHilbertFixedBaseProjection f a hL d V W t)

variable [Etale V.hom] [Etale W.hom] [IsAffine A.left] [IsAffine B.left]
  [IsOpenImmersion k.left] [IsOpenImmersion l.left]
local notation "v" => fixedBaseJointRelativeProjection f a hL d V W t c k l u hu
local notation "H" => fixedBaseJointProjection_condition f a hL d V W t c k l u hu
local instance jointOrbitSeedFinitePresentation : LocallyOfFinitePresentation (v).left :=
  fixedBaseJointProjection_locallyOfFinitePresentation f a hL d V W t c k l u hu

local notation "p₁" => Over.Hom.left (fst q h d W c' l)
local notation "q₁" => Over.Hom.left (snd q h d W c' l)
local notation "r₀" => fixedBaseJointToOld f a hL d V W t c k l u hu
local notation "r₁" => fixedBaseJointToNew f a hL d V W t c k l u hu
variable [IrreducibleSpace (fixedBaseJointOver f a hL d V W t c k l u hu).left]
  {Z : Scheme} (s : Z ⟶ B.left) [Etale s]
  [Etale (s ≫ (fixedBaseJointRelativeProjection f a hL d V W t c k l u hu).left)]
  [Mono (s ≫ (fixedBaseJointRelativeProjection f a hL d V W t c k l u hu).left)] [Nonempty Z]

/-- Original source orbits construct the generic kernel coverage needed by the joint model. -/
theorem fixedBaseJointFppfSource_nonempty_of_orbit_seed
    (hc : ∀ x : B.left, (v).left x =
      genericPoint (fixedBaseJointOver f a hL d V W t c k l u hu).left →
      ∃ z : Z, RelativeRelationOrbit.Related
        (fst q h d W c' l) (snd q h d W c' l) x (s z)) :
    Nonempty (modelFppfSource q h d W c' l v H).left := by
  apply fixedBaseJointFppfSource_nonempty_of_source_branch f a hL d V W t c k l u hu s
  exact (SchemeRelationMonicSeedKernel.generic_image_iff_orbits
    (equivalence q h d W c' l) (v).left H s).mpr hc

end FLT.Mazur.HilbertChart.AffineRestriction
