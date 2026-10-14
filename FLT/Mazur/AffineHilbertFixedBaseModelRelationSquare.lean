/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFixedBaseModelKernels

/-!
# The full relation square is Cartesian for changed coefficient models

The original Picard-section lifting theorem proves the relation/kernel square
is Cartesian on all scheme tests. The comparison of target models is only
assumed to commute with source maps; it is not assumed Cartesian.
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

variable {T : Over (Spec (.of R))} {T' : Over (Spec (.of R'))}
  (w : A ⟶ T) (v : B ⟶ T') (b : (Over.map a).obj T' ⟶ T)
  (hv : u ≫ w = (Over.map a).map v ≫ b)
local notation "p" => fst f hL d V c k
local notation "s" => snd f hL d V c k
local notation "p'" => fst q h d W c' l
local notation "s'" => snd q h d W c' l
variable (hw : (fst f hL d V c k).left ≫ w.left = (snd f hL d V c k).left ≫ w.left)
  (hv' : (fst (Limits.pullback.snd f a) (fixedBaseAmple f a hL) d W
    (fixedBaseTranslationClass f a V W t c) l).left ≫ v.left =
      (snd (Limits.pullback.snd f a) (fixedBaseAmple f a hL) d W
        (fixedBaseTranslationClass f a V W t c) l).left ≫ v.left)
local notation "r" => fixedBaseRelationMap f a hL d V W t c k l u hu
local notation "m" => modelRelationKernelMap f hL d V c k w.left hw
local notation "m'" => modelRelationKernelMap q h d W c' l v.left hv'

local notation "κ" => fixedBaseModelKernelMap a u w v b hv

/-- Every kernel test above an original Picard arrow has a unique changed Picard arrow. -/
theorem fixedBaseModelRelationSquare_lift {Z : Scheme}
    (x : Z ⟶ (relation f hL d V c k).left) (y : Z ⟶ pullback v.left v.left)
    (hxy : x ≫ m = y ≫ κ) :
    ∃! z : Z ⟶ (relation q h d W c' l).left,
      z ≫ (r).left = x ∧ z ≫ m' = y := by
  have hx : x ≫ (p).left = (y ≫ pullback.fst v.left v.left) ≫ u.left := by
    simpa only [Category.assoc, modelRelationKernelMap_fst,
      fixedBaseModelKernelMap_fst] using
        congrArg (fun z ↦ z ≫ pullback.fst w.left w.left) hxy
  have hy : x ≫ (s).left = (y ≫ pullback.snd v.left v.left) ≫ u.left := by
    simpa only [Category.assoc, modelRelationKernelMap_snd,
      fixedBaseModelKernelMap_snd] using
        congrArg (fun z ↦ z ≫ pullback.snd w.left w.left) hxy
  have hb : (y ≫ pullback.fst v.left v.left) ≫ B.hom =
      (y ≫ pullback.snd v.left v.left) ≫ B.hom := by
    rw [← v.w, ← Category.assoc _ v.left, ← Category.assoc _ v.left,
      Category.assoc y, Category.assoc y, pullback.condition]
    simp only [Category.assoc]
  obtain ⟨z, hz, _⟩ := fixedBaseRelationMap_scheme_lift f a hL d V W t c k l u hu
    (y ≫ pullback.fst v.left v.left) (y ≫ pullback.snd v.left v.left) hb x hx hy
  refine ⟨z, ⟨hz.2.2, ?_⟩, ?_⟩
  · apply pullback.hom_ext
    · rw [Category.assoc, modelRelationKernelMap_fst, hz.1]
    · rw [Category.assoc, modelRelationKernelMap_snd, hz.2.1]
  · intro z' hz'
    apply (cancel_mono m').mp
    exact hz'.2.trans (by
      apply pullback.hom_ext
      · rw [Category.assoc, modelRelationKernelMap_fst, hz.1]
      · rw [Category.assoc, modelRelationKernelMap_snd, hz.2.1])

/-- The full relation square, including nilpotents and both endpoints, is a pullback. -/
theorem fixedBaseModelRelationSquare_isPullback : IsPullback (r).left m' m κ := by
  let H (Z : Scheme) := fixedBaseModelRelationSquare_lift
    f a hL d V W t c k l u hu w v b hv hw hv' (Z := Z)
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (fixedBaseModelRelationSquare f a hL d V W t c k l u hu w v b hv hw hv')
    (fun c ↦ (H c.pt c.fst c.snd c.condition).choose)
    (fun c ↦ (H c.pt c.fst c.snd c.condition).choose_spec.1.1)
    (fun c ↦ (H c.pt c.fst c.snd c.condition).choose_spec.1.2) ?_)
  intro c z hz₁ hz₂
  exact (H c.pt c.fst c.snd c.condition).choose_spec.2 z ⟨hz₁, hz₂⟩

end FLT.Mazur.HilbertChart.AffineRestriction
