/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFixedBaseJointRelative
public import FLT.Mazur.RelativeCoefficientBaseChange

/-!
# Joint coefficients over the changed old ground target

The joint coefficient scheme maps to the actual ground-base pullback of the
old model. The source triangle keeps the new ground coordinate as well as
both old and newly recomputed coefficient systems.
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
local instance jointGroundOldSmooth : SmoothOfRelativeDimension 1 q :=
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
variable [Etale V.hom] [Etale W.hom] [IsAffine A.left] [IsAffine B.left]
  [IsOpenImmersion k.left] [IsOpenImmersion l.left]
local notation "J" => fixedBaseJointTarget f a hL d V W t c k l u hu
local notation "π" => fixedBaseJointProjection f a hL d V W t c k l u hu
local notation "r₀" => fixedBaseJointToOld f a hL d V W t c k l u hu
local notation "r₁" => fixedBaseJointToNew f a hL d V W t c k l u hu
local notation "M₀" => finiteKernelModel f hL d V c k
local notation "M₁" => finiteKernelModel q h d W c' l
local notation "v₁" => finiteKernelProjection q h d W c' l

/-- Compare with the old model while retaining the new ground coordinate. -/
def fixedBaseJointToGroundOld : J ⟶
    (RelativeCoefficientBaseChange.target a (T := M₀)).left :=
  (RelativeCoefficientBaseChange.projection a
    (fixedBaseJointRelativeToOld f a hL d V W t c k l u hu) (𝟙 M₀)).left

/-- The ground-aware comparison has the actual original coefficient triangle. -/
@[reassoc]
theorem fixedBaseJointToGroundOld_toOld :
    fixedBaseJointToGroundOld f a hL d V W t c k l u hu ≫
      (RelativeCoefficientBaseChange.toOld a (T := M₀)).left = r₀ := by
  exact pullback.lift_fst _ _ _

/-- The changed old target receives exactly the original source coefficients and ground map. -/
@[reassoc]
theorem fixedBaseJointProjection_toGroundOld :
    π ≫ fixedBaseJointToGroundOld f a hL d V W t c k l u hu =
      (RelativeCoefficientBaseChange.projection a u
        (finiteKernelProjection f hL d V c k)).left := by
  apply pullback.hom_ext
  · have hf : fixedBaseJointToGroundOld f a hL d V W t c k l u hu ≫
        pullback.fst (M₀).hom a = r₀ :=
      fixedBaseJointToGroundOld_toOld f a hL d V W t c k l u hu
    rw [Category.assoc, hf]
    rw [fixedBaseJointProjection_toOld]
    exact (pullback.lift_fst _ _ _).symm
  · change π ≫ (fixedBaseJointToGroundOld f a hL d V W t c k l u hu ≫
      pullback.snd (M₀).hom a) = _
    rw [show fixedBaseJointToGroundOld f a hL d V W t c k l u hu ≫
      pullback.snd (M₀).hom a = r₁ ≫ (M₁).hom from pullback.lift_snd _ _ _]
    rw [← Category.assoc, fixedBaseJointProjection_toNew, (v₁).w]
    exact (pullback.lift_snd _ _ _).symm

end FLT.Mazur.HilbertChart.AffineRestriction
