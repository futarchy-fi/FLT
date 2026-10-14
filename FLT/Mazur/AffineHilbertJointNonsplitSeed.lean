/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertJointSourceBranch
public import FLT.Mazur.SchemeRelationSeedGenericImage

/-!
# Joint coefficient neighborhoods from partial nonsplit seed certificates

Partial certificates on the generic seed kernel propagate through the original
relation to the full joint model kernel. The constructed represented source
retains both maps of the actual old/new coefficient comparison. Neither
coefficient self-change is assumed flat or covering.
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
local instance jointNonsplitSeedSmooth : SmoothOfRelativeDimension 1 q :=
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
local instance jointNonsplitSeedFinitePresentation : LocallyOfFinitePresentation (v).left :=
  fixedBaseJointProjection_locallyOfFinitePresentation f a hL d V W t c k l u hu

local notation "p₁" => Over.Hom.left (fst q h d W c' l)
local notation "q₁" => Over.Hom.left (snd q h d W c' l)
local notation "r₀" => fixedBaseJointToOld f a hL d V W t c k l u hu
local notation "r₁" => fixedBaseJointToNew f a hL d V W t c k l u hu
variable [IrreducibleSpace (fixedBaseJointOver f a hL d V W t c k l u hu).left]
  {Z : Scheme} (s : Z ⟶ B.left) [Etale s]
  [Etale (s ≫ (fixedBaseJointRelativeProjection f a hL d V W t c k l u hu).left)]
  [Nonempty Z]

/-- Generic seed certificates construct a represented source for the actual joint model. -/
theorem fixedBaseJointFppfSource_nonempty_of_nonsplit_seed
    (hs : ∀ z : (pullback (s ≫ (v).left) (s ≫ (v).left) : Scheme),
      (pullback.fst (s ≫ (v).left) (s ≫ (v).left) ≫ (s ≫ (v).left)) z =
        genericPoint (fixedBaseJointOver f a hL d V W t c k l u hu).left →
      z ∈ Set.range (SchemeRelationSeedKernelTransport.seedComparison (v).left H s))
    (hc : ∀ x : B.left, (v).left x =
      genericPoint (fixedBaseJointOver f a hL d V W t c k l u hu).left →
      ∃ z : Z, RelativeRelationOrbit.Related
        (fst q h d W c' l) (snd q h d W c' l) x (s z)) :
    Nonempty (modelFppfSource q h d W c' l v H).left := by
  apply fixedBaseJointFppfSource_nonempty_of_source_branch f a hL d V W t c k l u hu s
  exact SchemeRelationSeedKernelTransport.generic_image
    (equivalence q h d W c' l) (v).left H s hs hc

end FLT.Mazur.HilbertChart.AffineRestriction
