/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFixedBaseModelRelationSquare
public import FLT.Mazur.MonomorphismRelativeOpenTransport

/-!
# Old effective opens survive changed charts and coefficient models

The full Picard relation square is proved Cartesian, so every old effective
target open pulls into the new effective target open. This is valid for actual
changed ground bases and translations without flatness of the target map.
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

include hu hv in
/-- Old effective target neighborhoods remain effective after actual chart changes. -/
theorem fixedBaseModelEffectiveOpen_le :
    b.left ⁻¹ᵁ KernelPairEffectiveOpen.targetOpen (p).left (s).left w.left hw ≤
      KernelPairEffectiveOpen.targetOpen (p').left (s').left v.left hv' :=
  MonomorphismRelativeOpen.preimage_targetOpen_le m (pullback.fst w.left w.left ≫ w.left)
    (r).left m' κ (pullback.fst v.left v.left ≫ v.left) b.left
    (fixedBaseModelRelationSquare_isPullback f a hL d V W t c k l u hu w v b hv hw hv')
    (fixedBaseModelKernelMap_target a u w v b hv)

include hu hv in
/-- Global old kernel effectivity is inherited by the newly selected model. -/
theorem fixedBaseModelEffectiveOpen_top
    (he : KernelPairEffectiveOpen.targetOpen (p).left (s).left w.left hw = ⊤) :
    KernelPairEffectiveOpen.targetOpen (p').left (s').left v.left hv' = ⊤ := by
  apply top_le_iff.mp
  have hh := fixedBaseModelEffectiveOpen_le f a hL d V W t c k l u hu w v b hv hw hv'
  rw [he] at hh
  exact hh

end FLT.Mazur.HilbertChart.AffineRestriction
