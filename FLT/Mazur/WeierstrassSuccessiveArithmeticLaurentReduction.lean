/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveArithmeticTensorBranches
public import FLT.Mazur.WeierstrassSuccessiveLaurentSlopeReduction

/-!
# Arithmetic Laurent slope reductions with the original branch labels

Both full slopes retain their specified reductions and unit tangents
at every original arithmetic quotient order.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
open PolygonArithmeticStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] (π : R) (m : ℕ)

variable (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (hs : π ∣ s) (h2 : π ∣ W.a₂)
  (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q
local notation "J" => ideal Q (parameter R π m)

variable (f : SuccessiveIncidence.Coordinate (algebraMap R (Quotient R π m) π) →ₐ[Quotient R π m]
  (Quotient R π m)[T;T⁻¹])
local notation "v" => arithmeticBranchSlope π m W s b3 b4 b6 ha hs h2 h3 h4 h6
local notation "K" => Ideal.map (algebraMap Q Q[T;T⁻¹]) J
local notation "a" => algebraMap Q Q[T;T⁻¹] (q W.a₁)

/-- The original small label has slope in the arithmetic ideal. -/
theorem arithmeticLaurentSmallSlope_mem : f (v false) ∈ K :=
  laurentSmallSlope_mem (W.map q) (q s) (q π) (q b3) (q b4) (q b6) J
    (arithmeticParameterIdeal_nilpotent π m) (ha.map q)
    (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
    (arithmeticCoefficient_mem π m h3) (arithmeticCoefficient_mem π m h4)
    (arithmeticCoefficient_mem π m h6) f

/-- The original opposite label has slope congruent to minus a1. -/
theorem arithmeticLaurentOppositeSlope_add_mem : f (v true) + a ∈ K :=
  laurentOppositeSlope_add_mem (W.map q) (q s) (q π) (q b3) (q b4) (q b6) J
    (arithmeticParameterIdeal_nilpotent π m) (ha.map q)
    (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
    (arithmeticCoefficient_mem π m h3) (arithmeticCoefficient_mem π m h4)
    (arithmeticCoefficient_mem π m h6) f

/-- The small label has invertible opposite tangent over the whole quotient. -/
theorem arithmeticLaurentSmallSlope_add_unit : IsUnit (f (v false) + a) :=
  laurentSmallSlope_add_unit (W.map q) (q s) (q π) (q b3) (q b4) (q b6) J
    (arithmeticParameterIdeal_nilpotent π m) (ha.map q)
    (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
    (arithmeticCoefficient_mem π m h3) (arithmeticCoefficient_mem π m h4)
    (arithmeticCoefficient_mem π m h6) f

/-- The opposite label has invertible slope over the whole quotient. -/
theorem arithmeticLaurentOppositeSlope_unit : IsUnit (f (v true)) :=
  laurentOppositeSlope_unit (W.map q) (q s) (q π) (q b3) (q b4) (q b6) J
    (arithmeticParameterIdeal_nilpotent π m) (ha.map q)
    (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
    (arithmeticCoefficient_mem π m h3) (arithmeticCoefficient_mem π m h4)
    (arithmeticCoefficient_mem π m h6) f

end FLT.Mazur.WeierstrassSuccessiveX
