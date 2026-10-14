/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFixedBaseOldCoefficients
public import FLT.Mazur.AffineHilbertGroundBaseSource
public import FLT.Mazur.AffineHilbertMonicSeedFiniteEtale

/-!
# Constructed changed-ground charts on original monic-seed orbits

First select an actual affine open from the original seed orbit, then pull
that chart back along the new translation. Its old coefficient map is etale
and its complete changed Picard kernel is derived from the original seed.
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
local instance monicSeedGroundSmooth : SmoothOfRelativeDimension 1 q :=
  MorphismProperty.pullback_snd _ _ inferInstance
local notation "h" => fixedBaseAmple f a hL
local notation "c'" => fixedBaseTranslationClass f a V W t c
local notation "P" => variableHilbertFixedBaseProjection f a hL d V W t
variable {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
  [Etale V.hom] [Etale W.hom]
  {Z : Scheme} (s : Z ⟶ A.left) [Etale s]
  [Etale (s ≫ (finiteKernelProjection f hL d V c k).left)]
  [Mono (s ≫ (finiteKernelProjection f hL d V c k).left)]
  (z : (pullback (snd f hL d V c k).left s : Scheme))
local notation "v" => monicSeedAffineMap f hL d V c k s z
local notation "k₀" => monicSeedAffineChart f hL d V c k s z
local notation "w₀" => finiteKernelProjection f hL d V c k
local notation "hw₀" => congrArg Over.Hom.left (finiteKernelProjection_condition f hL d V c k)
local instance seedGroundSelectedOpen : IsOpenImmersion (k₀).left :=
  monicSeedAffineChart_isOpenImmersion f hL d V c k s z (w₀).left hw₀

/-- An actual changed-family chart constructed from the selected original seed orbit. -/
def monicSeedGroundSource : Over (Spec (.of R')) :=
  groundBaseSource f a hL d V W t k₀

/-- Its new Hilbert parameter map is the genuine ground-base source chart. -/
def monicSeedGroundChart : monicSeedGroundSource f a hL d V W t c k s z ⟶
    variableHilbertTest q d W := groundBaseSourceChart f a hL d V W t k₀

/-- The map to the original source retains the selected seed and original parameter. -/
def monicSeedGroundMap :
    (Over.map a).obj (monicSeedGroundSource f a hL d V W t c k s z) ⟶ A :=
  groundBaseSourceMap f a hL d V W t k₀ ≫ v

omit [IsAffine A.left] [IsOpenImmersion k.left] [Etale V.hom] [Etale W.hom]
  [Etale s] [Etale (s ≫ (finiteKernelProjection f hL d V c k).left)]
  [Mono (s ≫ (finiteKernelProjection f hL d V c k).left)] in
/-- The constructed maps satisfy the original Hilbert parameter square. -/
theorem monicSeedGround_square : monicSeedGroundMap f a hL d V W t c k s z ≫ k =
    (Over.map a).map (monicSeedGroundChart f a hL d V W t c k s z) ≫ P := by
  rw [monicSeedGroundMap, Category.assoc]
  exact groundBaseSource_square f a hL d V W t k₀

instance monicSeedGroundChart_isOpenImmersion :
    IsOpenImmersion (monicSeedGroundChart f a hL d V W t c k s z).left :=
  inferInstanceAs (IsOpenImmersion (groundBaseSourceChart f a hL d V W t k₀).left)

instance monicSeedGroundSource_isAffine [IsAffine V.left] [IsAffine W.left] :
    IsAffine (monicSeedGroundSource f a hL d V W t c k s z).left :=
  inferInstanceAs (IsAffine (groundBaseSource f a hL d V W t k₀).left)

local notation "u" => monicSeedGroundMap f a hL d V W t c k s z
local notation "l" => monicSeedGroundChart f a hL d V W t c k s z
local notation "b" => RelativeCoefficientBaseChange.projection a u w₀

omit [Etale W.hom] [Etale s]
  [Etale (s ≫ (finiteKernelProjection f hL d V c k).left)] in
/-- The COMPLETE changed relation is the old coefficient kernel with its new ground coordinate. -/
theorem monicSeedGroundOld_isPullback :
    IsPullback (fst q h d W c' l).left (snd q h d W c' l).left (b).left (b).left := by
  have H := monicSeedAffine_isPullback f hL d V c k (w₀).left hw₀ s z
  have hh := fixedBaseOldCoefficients_isPullback f a hL d V W t c k₀ l
    (groundBaseSourceMap f a hL d V W t k₀)
    (groundBaseSource_square f a hL d V W t k₀) (v ≫ w₀) H.w H
  simpa only [monicSeedGroundMap, RelativeCoefficientBaseChange.projection_comp] using hh

omit [Etale W.hom] [Etale s]
  [Mono (s ≫ (finiteKernelProjection f hL d V c k).left)] in
/-- The full selected source is etale over its actual ground-aware old coefficient target. -/
theorem monicSeedGroundOld_etale [Etale a] [Etale t.left] : Etale (b).left := by
  let _ : Etale (v ≫ w₀).left :=
    monicSeedAffineChart_target_etale f hL d V c k s z (w₀).left hw₀
  change Etale (RelativeCoefficientBaseChange.projection a
    (groundBaseSourceMap f a hL d V W t k₀ ≫ v) w₀).left
  rw [RelativeCoefficientBaseChange.projection_comp]
  infer_instance

end FLT.Mazur.HilbertChart.AffineRestriction
