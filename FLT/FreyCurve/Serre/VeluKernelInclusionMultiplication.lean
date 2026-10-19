/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluKernelPairDetection
public import FLT.Mazur.WeierstrassCoefficientAddition

/-!
# The rational kernel inclusion preserves multiplication

Each original pair retains its original affine group sections. Their sum and
coefficient compatibility establish the full multiplication equality by descent.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
open CartesianMonoidalCategory

namespace WeierstrassCurve.Velu

open FLT.Mazur FLT.Mazur.WeierstrassIntegralChart

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime]
  (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →ₗ[ZMod p] ZMod p)
  (hq : Function.Surjective q)
  (hfixed : ∀ g t, q (E.torsionGaloisRepresentation p g t) = q t)

local notation "K" => primeKernelRationalScheme E p q hq hfixed
local notation "I" => primeKernelRationalInclusion E p q hq hfixed
local notation "V" => E.map (algebraMap ℚ (AlgebraicClosure ℚ))
local notation "s" => affineRationalGroupSectionAddHom V
local notation "t" => primeKernelParam E p q hq

/-- On each original pair, the inclusion product is the original pair of cubic sections. -/
theorem primeKernelPairSection_inclusion_product (i j : ZMod p) :
    primeKernelPairSection E p q hq hfixed i j ≫ (I ⊗ₘ I).left =
      (lift (s (t i)).toMul (s (t j)).toMul).left ≫ integralCoefficientProduct E := by
  apply pullback.hom_ext
  · change primeKernelPairSection E p q hq hfixed i j ≫ (I ⊗ₘ I).left ≫
      (fst (integralGeneralizedEllipticCurve E E.isUnit_Δ).group
        (integralGeneralizedEllipticCurve E E.isUnit_Δ).group).left = _
    rw [← Over.comp_left, tensorHom_fst, Over.comp_left]
    change primeKernelPairSection E p q hq hfixed i j ≫ pullback.fst (K).hom (K).hom ≫
      (I).left = _
    rw [primeKernelPairSection_fst_assoc, Category.assoc]
    change _ = (lift (s (t i)).toMul (s (t j)).toMul).left ≫
      integralCoefficientProduct E ≫
        pullback.fst (integralCurveStructure E) (integralCurveStructure E)
    rw [integralCoefficientProduct_fst]
    change _ = (lift (s (t i)).toMul (s (t j)).toMul).left ≫
      (fst (integralGeneralizedEllipticCurve V (V).isUnit_Δ).group
        (integralGeneralizedEllipticCurve V (V).isUnit_Δ).group).left ≫
          integralCoefficientMorphism E
    rw [← Over.comp_left_assoc, lift_fst]
    exact (primeKernelRationalMap_section E p q hq hfixed i).symm
  · change primeKernelPairSection E p q hq hfixed i j ≫ (I ⊗ₘ I).left ≫
      (snd (integralGeneralizedEllipticCurve E E.isUnit_Δ).group
        (integralGeneralizedEllipticCurve E E.isUnit_Δ).group).left = _
    rw [← Over.comp_left, tensorHom_snd, Over.comp_left]
    change primeKernelPairSection E p q hq hfixed i j ≫ pullback.snd (K).hom (K).hom ≫
      (I).left = _
    rw [primeKernelPairSection_snd_assoc, Category.assoc]
    change _ = (lift (s (t i)).toMul (s (t j)).toMul).left ≫
      integralCoefficientProduct E ≫
        pullback.snd (integralCurveStructure E) (integralCurveStructure E)
    rw [integralCoefficientProduct_snd]
    change _ = (lift (s (t i)).toMul (s (t j)).toMul).left ≫
      (snd (integralGeneralizedEllipticCurve V (V).isUnit_Δ).group
        (integralGeneralizedEllipticCurve V (V).isUnit_Δ).group).left ≫
          integralCoefficientMorphism E
    rw [← Over.comp_left_assoc, lift_snd]
    exact (primeKernelRationalMap_section E p q hq hfixed j).symm

/-- The actual rational inclusion preserves multiplication as a full scheme morphism. -/
@[reassoc] theorem primeKernelRationalInclusion_multiplication :
    μ[K] ≫ I = (I ⊗ₘ I) ≫
      μ[(integralGeneralizedEllipticCurve E E.isUnit_Δ).group] := by
  apply Over.OverMorphism.ext
  apply primeKernelPairSection_hom_ext E p q hq hfixed
  intro i j
  change primeKernelPairSection E p q hq hfixed i j ≫ μ[K].left ≫ (I).left =
    primeKernelPairSection E p q hq hfixed i j ≫ (I ⊗ₘ I).left ≫ _
  rw [primeKernelPairSection_multiplication_assoc, ← Category.assoc,
    primeKernelPairSection_inclusion_product, Category.assoc]
  change _ = (lift (s (t i)).toMul (s (t j)).toMul).left ≫
    integralCoefficientProduct E ≫ integralCurveAddition E E.isUnit_Δ
  rw [← integralCoefficientMorphism_addition E E.isUnit_Δ (V).isUnit_Δ]
  change _ = (lift (s (t i)).toMul (s (t j)).toMul).left ≫
    μ[(integralGeneralizedEllipticCurve V (V).isUnit_Δ).group].left ≫
      integralCoefficientMorphism E
  rw [← Over.comp_left_assoc, ← Hom.mul_def]
  have hs : (s (t i)).toMul * (s (t j)).toMul = (s (t (i + j))).toMul := by
    rw [map_add, map_add]
    rfl
  rw [hs]
  exact (primeKernelRationalMap_section E p q hq hfixed (i + j)).symm

/-- The original rational kernel inclusion is a homomorphism of group objects. -/
instance primeKernelRationalInclusion_isMonHom : IsMonHom I where
  one_hom := primeKernelRationalInclusion_identity E p q hq hfixed
  mul_hom := primeKernelRationalInclusion_multiplication E p q hq hfixed

end WeierstrassCurve.Velu
