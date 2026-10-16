/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXPolynomialFactorRatioNaturality
public import FLT.Mazur.NodalFiberUnitScalingGeometry

/-!
# Coefficient squares for the whole corrected polygon chart

The original arithmetic map commutes with the corrected node isomorphism,
the normalized tangent inclusion, and the complete polygon comparison.
-/

@[expose] public noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  (W : WeierstrassCurve R) (ha : IsUnit W.a₁) (s τ : R)
  (hτ : s = W.a₁ ^ 2 * τ) (τ' : S) (hτ' : f s = (W.map f).a₁ ^ 2 * τ') (ht : f τ = τ')
  (b3 b4 b6 : R) (r : R[X])
  (hr : r ^ 2 + polynomialSlopeLinear W b3 * r = polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (J : Ideal S) (hf : I ≤ J.comap f)
  (hI : IsNilpotent I) (hJ : IsNilpotent J) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
local notation "U" => W.map f
local notation "hrJ" => polynomialArithmeticIdeal_coefficient f I J hf hrI
local notation "hr'" => polynomialRootEquation_coefficient f W b3 b4 b6 r hr
local notation "E" => polynomialFactorRatioIso W ha s τ hτ b3 b4 b6 r hr I hI hrI h3
local notation "E'" => polynomialFactorRatioIso U (ha.map f) (f s) τ' hτ'
  (f b3) (f b4) (f b6) (r.map f) hr' J hJ hrJ (hf h3)
local notation "g" => nodeOpenCoefficientRingMap f W s
local notation "d" => NodalFiber.tangentCoefficientRingMap f τ (-1 : R) τ' (-1 : S) ht (by simp)

/-- The corrected whole polygon chart follows the original arithmetic coefficient map. -/
@[reassoc] theorem polynomialFactorRatioChart_coefficient :
    Spec.map (CommRingCat.ofHom g) ≫
      polynomialFactorRatioChart W ha s τ hτ b3 b4 b6 r hr I hI hrI h3 =
        polynomialFactorRatioChart U (ha.map f) (f s) τ' hτ'
          (f b3) (f b4) (f b6) (r.map f) hr' J hJ hrJ (hf h3) ≫
            Spec.map (CommRingCat.ofHom (PolygonSmoothing.ringMap f τ τ' ht)) := by
  have hd : Spec.map (CommRingCat.ofHom d) ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap (NodalFiber.Coordinate τ) (NodalFiber.TangentOpen τ (-1 : R)))) =
      Spec.map (CommRingCat.ofHom
        (algebraMap (NodalFiber.Coordinate τ') (NodalFiber.TangentOpen τ' (-1 : S)))) ≫
      Spec.map (CommRingCat.ofHom (NodalFiber.coefficientRingMap f τ τ' ht)) := by
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun k ↦ Spec.map (CommRingCat.ofHom k))
      (RingHom.ext (NodalFiber.tangentCoefficientRingMap_base f τ (-1) τ' (-1) ht (by simp)))
  simp only [polynomialFactorRatioChart, ← Category.assoc]
  rw [polynomialFactorRatioIso_hom_coefficient f W ha s τ hτ τ' hτ' ht
    b3 b4 b6 r hr I J hf hI hJ hrI h3]
  simp only [Category.assoc]
  rw [← Category.assoc (Spec.map (CommRingCat.ofHom d)), hd, Category.assoc]
  rw [NodalFiber.unitSmoothingIso_coefficients τ τ 1 (by simp) f
    τ' τ' 1 (by simp) ht ht (by simp)]

end FLT.Mazur.WeierstrassModificationX
