/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertGroundRelativeEtale
public import FLT.Mazur.RelativeCoefficientSourceImage

/-!
# Complete source and coefficient coverage after arbitrary ground changes

A surjective relative translation preserves every original chart point with
its compatible new ground coordinate. For seed selections, the changed old
coefficient image is the entire ground pullback of the SELECTED old image.
This does not construct initial seeds outside that selected chart.
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
local instance groundRelativeCoverageSmooth : SmoothOfRelativeDimension 1 q :=
  MorphismProperty.pullback_snd _ _ inferInstance
variable {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
  [Surjective (RelativeCoefficientBaseChange.projection a t (𝟙 V)).left]
local notation "u₀" => groundBaseSourceMap f a hL d V W t k
local notation "b₀" => groundBaseSourceChart f a hL d V W t k ≫ variableHilbertBase q d W

/-- Relative translation coverage constructs coverage of the entire changed original source. -/
theorem groundBaseSource_relative_surjective :
    Surjective (RelativeCoefficientBaseChange.projection a u₀ (𝟙 A)).left :=
  RelativeCoefficientBaseChange.relativeSource_surjective a u₀ b₀
    (k ≫ variableHilbertBase f d V) t (groundBaseSource_isPullback f a hL d V W t k)

/-- Compatible old chart and new ground points lift, without requiring an absolute etale map. -/
theorem groundBaseSource_exists_point_of_relative_surjective (x : A.left) (y : Spec (.of R'))
    (hxy : A.hom x = a y) :
    ∃ z : (groundBaseSource f a hL d V W t k).left,
      (u₀).left z = x ∧ (groundBaseSource f a hL d V W t k).hom z = y := by
  let _ := groundBaseSource_relative_surjective f a hL d V W t k
  exact RelativeCoefficientBaseChange.relativeSource_exists_point a u₀ x y hxy

variable [Etale V.hom] [Etale W.hom]

/-- Every test of the complete changed source has a surjective etale cover by the new chart. -/
theorem groundBaseSource_relative_test_cover {Y : Scheme}
    (b : Y ⟶ (RelativeCoefficientBaseChange.target a (T := A)).left) :
    Etale (pullback.snd (RelativeCoefficientBaseChange.projection a u₀ (𝟙 A)).left b) ∧
    Surjective (pullback.snd (RelativeCoefficientBaseChange.projection a u₀ (𝟙 A)).left b) := by
  let _ := groundBaseSource_relative_etale f a hL d V W t k
  let _ := groundBaseSource_relative_surjective f a hL d V W t k
  exact ⟨inferInstance, inferInstance⟩

/-- The full old image pulls back as an OPEN SUBSCHEME, with its nilpotents retained. -/
theorem groundBaseSource_coefficients_image {T : Over (Spec (.of R))}
    (w : A ⟶ T) [Etale w.left] :
    let _ := groundBaseSource_coefficients_etale f a hL d V W t k w
    SchemeEtaleImageQuotient.image (RelativeCoefficientBaseChange.projection a u₀ w).left =
      (RelativeCoefficientBaseChange.toOld a (T := T)).left ⁻¹ᵁ
        SchemeEtaleImageQuotient.image w.left := by
  let _ := groundBaseSource_relative_etale f a hL d V W t k
  let _ := groundBaseSource_relative_surjective f a hL d V W t k
  exact RelativeCoefficientBaseChange.projection_image_of_relative_surjective a u₀ w

variable (c : (relativeFppfSheaf f).obj.obj (op V))
  [IsAffine A.left] [IsOpenImmersion k.left]
  {Z : Scheme} (s : Z ⟶ A.left)
  [Etale (s ≫ (finiteKernelProjection f hL d V c k).left)]
  (z : (pullback (snd f hL d V c k).left s : Scheme))
local notation "v" => monicSeedAffineMap f hL d V c k s z
local notation "k₀" => monicSeedAffineChart f hL d V c k s z
local notation "w₀" => finiteKernelProjection f hL d V c k
local notation "u" => monicSeedGroundMap f a hL d V W t c k s z
local instance groundCoverageSeedTargetEtale : Etale (v ≫ w₀).left :=
  monicSeedAffineChart_target_etale f hL d V c k s z (w₀).left
    (congrArg Over.Hom.left (finiteKernelProjection_condition f hL d V c k))
local instance groundCoverageChangedTargetEtale :
    Etale (RelativeCoefficientBaseChange.projection a u w₀).left :=
  monicSeedGroundOld_etale_arbitrary f a hL d V W t k c s z

/-- Surjective relative translations retain the ENTIRE changed image of the selected seed chart. -/
theorem monicSeedGround_image_eq_preimage :
    SchemeEtaleImageQuotient.image (RelativeCoefficientBaseChange.projection a u w₀).left =
      (RelativeCoefficientBaseChange.toOld a
        (T := finiteKernelModel f hL d V c k)).left ⁻¹ᵁ
          SchemeEtaleImageQuotient.image (v ≫ w₀).left := by
  simpa only [monicSeedGroundMap, RelativeCoefficientBaseChange.projection_comp] using
    groundBaseSource_coefficients_image f a hL d V W t k₀ (v ≫ w₀)

end FLT.Mazur.HilbertChart.AffineRestriction
