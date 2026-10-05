/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorPowerEulerCharacteristic
public import FLT.Mazur.TensorPowerDistribution

/-!
# Degree of a line presented as a difference of effective divisors

An actual isomorphism O(D) ⊗ L ≅ O(E), with D and E finite, gives the
Euler-characteristic power formula for L. The presentation is geometric data;
its existence for an arbitrary line on an integral proper curve is not assumed
as an instance or incorporated into the definition of a line sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.FCurve

open ModuleSheafTensor ModuleSheafTensorAssociator ModuleLineBundleTensorPullback

variable {k : Type} [Field k] {X : Scheme}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
  {I : X.IdealSheafData} (hI : EffectiveCartier I) [IsFinite (I.subschemeι ≫ f)]
  {L : X.Modules} (hL : LocallyFreeRankOne L)

include hL in
/-- Repeated effective-divisor twists increase Euler characteristic by exponent times length. -/
theorem curveEulerCharacteristic_divisor_power_tensor (n : ℕ) :
    curveEulerCharacteristic f (tensor (tensorPower (divisorLineBundle I hI) n) L) =
      curveEulerCharacteristic f L + (n : ℤ) * (divisorFieldLength f I : ℤ) := by
  induction n with
  | zero =>
    change curveEulerCharacteristic f (tensor (structureModule X) L) = _
    rw [Nat.cast_zero, zero_mul, add_zero]
    exact curveEulerCharacteristic_iso f (leftUnitor L)
  | succ n ih =>
    change curveEulerCharacteristic f
      (tensor (tensor (divisorLineBundle I hI)
        (tensorPower (divisorLineBundle I hI) n)) L) = _
    rw [curveEulerCharacteristic_iso f
      (associator (divisorLineBundle I hI) (tensorPower (divisorLineBundle I hI) n) L),
      curveEulerCharacteristic_divisor_tensor f hI
        ((hI.divisorLineBundle_locallyFreeRankOne.tensorPower n).tensor hL), ih]
    push_cast
    ring

variable {J : X.IdealSheafData} (hJ : EffectiveCartier J) [IsFinite (J.subschemeι ≫ f)]
  (e : tensor (divisorLineBundle I hI) L ≅ divisorLineBundle J hJ)

include hL e in
/-- An actual difference-of-divisors presentation computes the degree of its line. -/
theorem curveSheafDegree_of_divisor_presentation :
    curveSheafDegree f L = (divisorFieldLength f J : ℤ) - divisorFieldLength f I := by
  have he := curveSheafDegree_iso f e
  rw [curveSheafDegree_divisor_tensor f hI hL, divisor_degree_eq_fieldLength f hJ] at he
  omega

include hL e in
/-- The Euler-characteristic power formula follows from a finite divisor presentation. -/
theorem curveEulerCharacteristic_power_of_divisor_presentation (n : ℕ) :
    curveEulerCharacteristic f (tensorPower L n) =
      (n : ℤ) * curveSheafDegree f L + curveEulerCharacteristic f (structureModule X) := by
  let en : tensor (tensorPower (divisorLineBundle I hI) n) (tensorPower L n) ≅
      tensorPower (divisorLineBundle J hJ) n :=
    tensorPowerDistributionIso _ _ n ≪≫ tensorPowerCongr e n
  have he := curveEulerCharacteristic_iso f en
  rw [curveEulerCharacteristic_divisor_power_tensor f hI (hL.tensorPower n),
    curveEulerCharacteristic_divisor_power f hJ n] at he
  rw [curveSheafDegree_of_divisor_presentation f hI hL hJ e]
  nlinarith

include hL e in
/-- Degree multiplies by the exponent for a line with an actual finite divisor presentation. -/
theorem curveSheafDegree_power_of_divisor_presentation (n : ℕ) :
    curveSheafDegree f (tensorPower L n) = (n : ℤ) * curveSheafDegree f L := by
  change curveEulerCharacteristic f (tensorPower L n) -
    curveEulerCharacteristic f (structureModule X) = _
  rw [curveEulerCharacteristic_power_of_divisor_presentation f hI hL hJ e n]
  exact add_sub_cancel_right _ _

end FLT.Mazur.FCurve
