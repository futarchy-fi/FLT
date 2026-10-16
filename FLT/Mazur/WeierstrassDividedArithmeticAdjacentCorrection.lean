/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRetainedAdjacentFactors
public import FLT.Mazur.WeierstrassDividedArithmeticAdjacentSlope

/-!
# Full corrections on the actual consecutive arithmetic retained nodes

The original consecutive Data prove all division identities. Each quotient
uses its independently constructed units, with the actual powers of π.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX PolygonArithmeticStages PolygonSmoothing
  WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) (k : ℕ)
  (d : Data W π (k + 1)) (e : Data W π (k + 1 + 1)) (m : ℕ)
  (ha : IsUnit W.a₁) (hs : π ∣ π ^ k) (h2 : π ∣ W.a₂)
  (hd3 : π ∣ d.b3) (hd4 : π ∣ d.b4) (hd6 : π ∣ d.b6)
  (he3 : π ∣ e.b3) (he4 : π ∣ e.b4) (he6 : π ∣ e.b6)
  (hsNext : π ∣ π ^ (k + 1))
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q
local notation "J" => ideal Q (parameter R π m)

local notation "V" => retainedFactorCorrectionUnit (W.map q) (q π) (q (π ^ k))
  (q d.b3) (q d.b4) (q d.b6) J (arithmeticParameterIdeal_nilpotent π m) (ha.map q)
  (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
  (arithmeticCoefficient_mem π m hd3) (arithmeticCoefficient_mem π m hd4)
  (arithmeticCoefficient_mem π m hd6)
local notation "V'" => retainedFactorCorrectionUnit (W.map q) (q π) (q (π ^ (k + 1)))
  (q e.b3) (q e.b4) (q e.b6) J (arithmeticParameterIdeal_nilpotent π m) (ha.map q)
  (arithmeticCoefficient_mem π m hsNext) (arithmeticCoefficient_mem π m h2)
  (arithmeticCoefficient_mem π m he3) (arithmeticCoefficient_mem π m he4)
  (arithmeticCoefficient_mem π m he6)
attribute [local irreducible] retainedFactorCorrectionUnit

include hπ in
/-- The full correction units agree at every original consecutive arithmetic retained edge. -/
theorem arithmeticRetainedCorrection_adjacent :
    Units.map (leftLaurentMap (q π)).toMonoidHom V =
      Units.map (retainedPrecedingEvaluation (q π)).toMonoidHom V' := by
  have h3 := factor3_step hπ d e
  have h4 := factor4_step hπ d e
  have h6 := factor6_step hπ d e
  have h := retainedFactorCorrectionUnit_adjacent (W.map q) (q π) (q (π ^ k))
    (q e.b3) (q e.b4) (q e.b6) J (arithmeticParameterIdeal_nilpotent π m) (ha.map q)
    (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
    (arithmeticCoefficient_mem π m he3) (arithmeticCoefficient_mem π m he4)
    (arithmeticCoefficient_mem π m he6)
  simpa only [h3, h4, h6, pow_succ', map_mul, map_pow] using h

include hπ in
/-- The outgoing full inverse correction is the next incoming inverse at the actual order. -/
theorem arithmeticRetainedCorrection_inv_adjacent :
    leftLaurentMap (q π) (↑V⁻¹ : ChartRing (q π)) =
      retainedPrecedingEvaluation (q π) (↑(V')⁻¹ : ChartRing (q π)) :=
  congrArg (fun z : Q[T;T⁻¹]ˣ ↦ (↑z⁻¹ : Q[T;T⁻¹]))
    (arithmeticRetainedCorrection_adjacent hπ k d e m ha hs h2 hd3 hd4 hd6
      he3 he4 he6 hsNext)

end FLT.Mazur.WeierstrassDividedDepth
