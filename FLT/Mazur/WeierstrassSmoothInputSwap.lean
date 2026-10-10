/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothFactorAddition
public import FLT.Mazur.WeierstrassAffineProductSwap

/-!
# Interchanging the factors of the full smooth product

The original input interchange preserves the actual smooth open. Its
restriction is involutive and agrees with categorical factor interchange.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Swapping projective inputs preserves the actual smooth-pair open. -/
theorem integralCurveSwap_preimage_smooth :
    integralCurveSwap W ⁻¹ᵁ smoothCurveProductOpen W = smoothCurveProductOpen W := by
  simp only [smoothCurveProductOpen, Scheme.Hom.preimage_inf,
    ← Scheme.Hom.comp_preimage, integralCurveSwap_fst, integralCurveSwap_snd, inf_comm]

/-- Restrict the original swap to the full smooth product. -/
def smoothProductSwap :
    (smoothCurveProductOpen W).toScheme ⟶ (smoothCurveProductOpen W).toScheme :=
  IsOpenImmersion.lift (smoothCurveProductOpen W).ι
    ((smoothCurveProductOpen W).ι ≫ integralCurveSwap W) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨p, rfl⟩
      exact (integralCurveSwap_preimage_smooth W).ge p.property)

/-- Smooth interchange retains the original global pair interchange. -/
@[reassoc] theorem smoothProductSwap_inclusion :
    smoothProductSwap W ≫ (smoothCurveProductOpen W).ι =
      (smoothCurveProductOpen W).ι ≫ integralCurveSwap W := IsOpenImmersion.lift_fac _ _ _

/-- The smooth swap is involutive. -/
@[reassoc] theorem smoothProductSwap_swap :
    smoothProductSwap W ≫ smoothProductSwap W = 𝟙 _ := by
  apply (cancel_mono (smoothCurveProductOpen W).ι).mp
  rw [Category.assoc, smoothProductSwap_inclusion,
    smoothProductSwap_inclusion_assoc, integralCurveSwap_swap,
    Category.comp_id, Category.id_comp]

/-- Interchange the factors of the categorical smooth product. -/
def smoothFactorSwap : smoothFactorProduct W ⟶ smoothFactorProduct W :=
  pullback.lift (pullback.snd _ _) (pullback.fst _ _) pullback.condition.symm

/-- The categorical swap preserves the original projective interchange. -/
@[reassoc] theorem smoothFactorSwap_inclusion :
    smoothFactorSwap W ≫ smoothFactorsInclusion W =
      smoothFactorsInclusion W ≫ integralCurveSwap W := by
  apply pullback.hom_ext
  · simp only [Category.assoc, smoothFactorsInclusion, pullback.lift_fst,
      integralCurveSwap_fst, pullback.lift_snd, smoothFactorSwap, pullback.lift_fst_assoc]
  · simp only [Category.assoc, smoothFactorsInclusion, pullback.lift_snd,
      integralCurveSwap_snd, pullback.lift_fst, smoothFactorSwap, pullback.lift_snd_assoc]

/-- The product isomorphism respects interchange. -/
@[reassoc] theorem smoothFactorSwap_toProduct :
    smoothFactorSwap W ≫ smoothFactorsToProduct W =
      smoothFactorsToProduct W ≫ smoothProductSwap W := by
  apply (cancel_mono (smoothCurveProductOpen W).ι).mp
  rw [Category.assoc, smoothFactorsToProduct_inclusion, smoothFactorSwap_inclusion,
    Category.assoc, smoothProductSwap_inclusion, smoothFactorsToProduct_inclusion_assoc]

/-- Affine interchange preserves smoothness of both inputs. -/
theorem affineInputSwap_preimage_smooth :
    affineInputSwap W ⁻¹ᵁ smoothAffineInputOpen W = smoothAffineInputOpen W := by
  rw [← smoothProductChartOpen_affine]
  change affineInputSwap W ⁻¹ᵁ
    (integralCurveProductChart W false false ⁻¹ᵁ smoothCurveProductOpen W) = _
  rw [← Scheme.Hom.comp_preimage]
  have hs : affineInputSwap W ≫ integralCurveProductChart W false false =
      integralCurveProductChart W false false ≫ integralCurveSwap W :=
    (integralCurveProductChart_swap W false false).symm
  rw [hs, Scheme.Hom.comp_preimage, integralCurveSwap_preimage_smooth]
  rfl

/-- The actual smooth affine input interchange. -/
def smoothAffineSwap :
    (smoothAffineInputOpen W).toScheme ⟶ (smoothAffineInputOpen W).toScheme :=
  IsOpenImmersion.lift (smoothAffineInputOpen W).ι
    ((smoothAffineInputOpen W).ι ≫ affineInputSwap W) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨p, rfl⟩
      exact (affineInputSwap_preimage_smooth W).ge p.property)

/-- Smooth affine interchange retains the original tensor interchange. -/
@[reassoc] theorem smoothAffineSwap_inclusion :
    smoothAffineSwap W ≫ (smoothAffineInputOpen W).ι =
      (smoothAffineInputOpen W).ι ≫ affineInputSwap W := IsOpenImmersion.lift_fac _ _ _

end FLT.Mazur.WeierstrassIntegralChart
