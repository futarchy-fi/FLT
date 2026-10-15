/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticInitialSlope
public import FLT.Mazur.WeierstrassDividedInitialTensorSlopeGeometry
public import FLT.Mazur.WeierstrassModificationXTensorLaurentEvaluation

/-!
# The original initial tensor boundary equals its independent arithmetic chart

This identifies every original tensor function, not only its two named
coordinates. The initial root is constructed from the initial coefficients.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX PolygonArithmeticStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k : ℕ}
  (d : Data W π k) (e : Data W π (k + 1)) (m : ℕ)
  (ha : IsUnit W.a₁) (hs : π ∣ π ^ k) (h2 : π ∣ W.a₂)
  (hd3 : π ∣ d.b3) (hd4 : π ∣ d.b4) (hd6 : π ∣ d.b6)
  (he3 : π ∣ e.b3) (he4 : π ∣ e.b4) (he6 : π ∣ e.b6)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q
local notation "J" => ideal Q (parameter R π m)
local notation "v₀" => laurentBranchSlope (W.map q) (q (π ^ k)) (q (Data.b3 d))
  (q (Data.b4 d)) (q (Data.b6 d)) J (arithmeticParameterIdeal_nilpotent π m) (ha.map q)
  (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
  (arithmeticCoefficient_mem π m hd3) (arithmeticCoefficient_mem π m hd4)
  (arithmeticCoefficient_mem π m hd6)

variable (opposite : Bool)
local notation "v₁" => arithmeticBranchSlope π m W (π ^ k) (Data.b3 e) (Data.b4 e)
  (Data.b6 e) ha hs h2 he3 he4 he6 opposite
local notation "hv₁" => arithmeticBranchSlope_equation π m W (π ^ k) (Data.b3 e) (Data.b4 e)
  (Data.b6 e) ha hs h2 he3 he4 he6 opposite
local notation "hv₀" => laurentBranchSlope_equation (W.map q) (q (π ^ k)) (q (Data.b3 d))
  (q (Data.b4 d)) (q (Data.b6 d)) J (arithmeticParameterIdeal_nilpotent π m) (ha.map q)
  (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
  (arithmeticCoefficient_mem π m hd3) (arithmeticCoefficient_mem π m hd4)
  (arithmeticCoefficient_mem π m hd6) opposite
local notation "E" => tensorLaurentSlopeEvaluation W (π ^ k) (Data.b3 d) (Data.b4 d)
  (Data.b6 d) Q (v₀ opposite) hv₀

/-- The entire original initial tensor transition is the independently constructed root map. -/
theorem arithmeticInitialTensor_evaluation :
    initialTensorSlopeRetraction hπ d e Q v₁ hv₁ = E := by
  apply tensorEvaluation_ext
  · rw [initialTensorSlopeRetraction_t, tensorLaurentSlopeEvaluation_t]
  · rw [initialTensorSlopeRetraction_v, tensorLaurentSlopeEvaluation_v]
    exact arithmeticInitialBranchSlope hπ d e m ha hs h2 hd3 hd4 hd6 he3 he4 he6 opposite

local notation "x" => WeierstrassDilatation.x W (π ^ k) (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "t₀" => t W (π ^ k) (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "u₁" => coord W (π ^ k) π (Data.b3 e) (Data.b4 e) (Data.b6 e) 2
local notation "a" => overlapEquiv W (π ^ k) (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "b" => previousBoundaryEquiv hπ d e

/-- On spectra the independent initial arithmetic chart retains both original transitions. -/
theorem arithmeticInitialTensor_boundary :
    Spec.map (CommRingCat.ofHom (E).toRingHom) =
      tensorSlopeRightBoundary W (π ^ k) π e.b3 e.b4 e.b6 Q v₁ hv₁ ≫
        (PrincipalOpenTensor.transitionIso Q x u₁ b).hom ≫
          (PrincipalOpenTensor.transitionIso Q x t₀ a).inv ≫
            PrincipalOpenTensor.inclusion Q t₀ := by
  rw [← arithmeticInitialTensor_evaluation hπ d e m ha hs h2
    hd3 hd4 hd6 he3 he4 he6 opposite]
  exact initialTensorSlopeRetraction_spec hπ d e Q v₁ hv₁

end FLT.Mazur.WeierstrassDividedDepth
