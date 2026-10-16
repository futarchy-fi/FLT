/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXArithmeticInitialFactorRatio

/-!
# Nilpotence of the constructed arithmetic polygon smoothing

The normalized scale lies in the original arithmetic parameter ideal. Thus
positive starting thickness supplies nilpotence without replacing the scale by π.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassModificationX
open PolygonArithmeticStages WeierstrassSuccessiveX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁)
  (s : R) (I : Ideal R)

include ha in
/-- Tangent normalization preserves membership in the actual coefficient ideal. -/
theorem initialTangentSmoothing_mem (hs : s ∈ I) : initialTangentSmoothing W ha s ∈ I :=
  I.mul_mem_left _ hs

/-- Nilpotence of the original ideal proves nilpotence of the exact normalized smoothing. -/
theorem initialTangentSmoothing_nilpotent (hI : IsNilpotent I) (hs : s ∈ I) :
    IsNilpotent (initialTangentSmoothing W ha s) :=
  NilpotentQuadraticRoot.element_nilpotent I hI (initialTangentSmoothing_mem W ha s I hs)

variable (π : R) (m : ℕ)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q
local notation "J" => ideal Q (parameter R π m)

/-- The actual arithmetic normalized smoothing belongs to the original parameter ideal. -/
theorem arithmeticInitialFactorRatioSmoothing_mem (hs : π ∣ s) :
    arithmeticInitialMobiusSmoothing W ha s π m ∈ J :=
  initialTangentSmoothing_mem (W.map q) (ha.map q) (q s) J
    (arithmeticCoefficient_mem π m hs)

/-- Every arithmetic order has nilpotent corrected smoothing from the original ideal. -/
theorem arithmeticInitialFactorRatioSmoothing_nilpotent (hs : π ∣ s) :
    IsNilpotent (arithmeticInitialMobiusSmoothing W ha s π m) :=
  NilpotentQuadraticRoot.element_nilpotent J (arithmeticParameterIdeal_nilpotent π m)
    (arithmeticInitialFactorRatioSmoothing_mem W ha s π m hs)

/-- Any positive starting thickness gives the required nilpotence at every quotient order. -/
theorem arithmeticInitialFactorRatioSmoothing_pow_nilpotent (start : ℕ) (hstart : 0 < start) :
    IsNilpotent (arithmeticInitialMobiusSmoothing W ha (π ^ start) π m) :=
  arithmeticInitialFactorRatioSmoothing_nilpotent W ha (π ^ start) π m
    (dvd_pow_self π (Nat.ne_of_gt hstart))

end FLT.Mazur.WeierstrassModificationX
