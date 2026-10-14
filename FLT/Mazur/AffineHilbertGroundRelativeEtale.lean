/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertMonicSeedGroundSource
public import FLT.Mazur.RelativeCoefficientSourceCartesian

/-!
# Etale selected sources after arbitrary ground changes

The Cartesian Hilbert translation square constructs relative etaleness.
In particular, the old coefficient maps on actual changed monic-seed charts
are etale even when the ground and absolute translation maps are not.
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
  (t : (Over.map a).obj W ⟶ V)
local notation "q" => Limits.pullback.snd f a
local instance groundRelativeEtaleSmooth : SmoothOfRelativeDimension 1 q :=
  MorphismProperty.pullback_snd _ _ inferInstance
variable {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
  [Etale V.hom] [Etale W.hom]
local notation "u₀" => groundBaseSourceMap f a hL d V W t k

/-- The constructed source is etale over the actual ground pullback of the original source. -/
theorem groundBaseSource_relative_etale :
    Etale (RelativeCoefficientBaseChange.projection a u₀ (𝟙 A)).left :=
  RelativeCoefficientBaseChange.relativeSource_etale a u₀
    (groundBaseSourceChart f a hL d V W t k ≫ variableHilbertBase q d W)
    (k ≫ variableHilbertBase f d V) t (groundBaseSource_isPullback f a hL d V W t k)

/-- Every old etale coefficient map stays etale on the complete changed source. -/
theorem groundBaseSource_coefficients_etale {T : Over (Spec (.of R))}
    (w : A ⟶ T) [Etale w.left] :
    Etale (RelativeCoefficientBaseChange.projection a u₀ w).left := by
  let _ := groundBaseSource_relative_etale f a hL d V W t k
  exact RelativeCoefficientBaseChange.projection_etale_of_relative a u₀ w

variable (c : (relativeFppfSheaf f).obj.obj (op V))
  [IsAffine A.left] [IsOpenImmersion k.left]
  {Z : Scheme} (s : Z ⟶ A.left)
  [Etale (s ≫ (finiteKernelProjection f hL d V c k).left)]
  (z : (pullback (snd f hL d V c k).left s : Scheme))
local notation "v" => monicSeedAffineMap f hL d V c k s z
local notation "k₀" => monicSeedAffineChart f hL d V c k s z
local notation "w₀" => finiteKernelProjection f hL d V c k

/-- Seed geometry derives etaleness over the ground-aware old target for ANY ground map. -/
theorem monicSeedGroundOld_etale_arbitrary :
    Etale (RelativeCoefficientBaseChange.projection a
      (monicSeedGroundMap f a hL d V W t c k s z) w₀).left := by
  let _ : Etale (v ≫ w₀).left :=
    monicSeedAffineChart_target_etale f hL d V c k s z (w₀).left
      (congrArg Over.Hom.left (finiteKernelProjection_condition f hL d V c k))
  change Etale (RelativeCoefficientBaseChange.projection a
    (groundBaseSourceMap f a hL d V W t k₀ ≫ v) w₀).left
  rw [RelativeCoefficientBaseChange.projection_comp]
  exact groundBaseSource_coefficients_etale f a hL d V W t k₀ (v ≫ w₀)

end FLT.Mazur.HilbertChart.AffineRestriction
