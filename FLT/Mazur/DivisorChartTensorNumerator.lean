/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorChartNumerator
public import FLT.Mazur.DivisorPowerCanonicalSection

/-!
# Degree-bounded numerators of the original tensor sections

On a specified whole Cartier chart, a section of O(dD) has a numerator
with denominator exactly the d-th power of the original equation. The section
is retained through the actual divisor-power comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
universe u
variable {X : Scheme.{u}} {I : X.IdealSheafData} (hI : EffectiveCartier I)
variable (U : X.affineOpens) (a : Γ(X, U)) (ha : IsRegular a)
variable (he : I.ideal U = Ideal.span {a})

/-- A specified equation bounds the denominator of a positive divisor section by one. -/
theorem divisorNumerator_smul (s : Γ(divisorLineBundle I hI, U.1)) :
    a • s = divisorNumerator hI U a ha he s • divisorSection hI U.1 := by
  apply (divisorNumerator hI U a ha he).injective
  rw [LinearEquiv.map_smul, divisorNumerator_canonical, smul_eq_mul, mul_comm]

include he in
/-- The full power ideal has the specified power equation on the same entire chart. -/
theorem divisorChart_power_equation (d : ℕ) :
    (I ^ d).ideal U = Ideal.span {a ^ d} := by
  change I.ideal U ^ d = _
  rw [he, Ideal.span_singleton_pow]

/-- The numerator of the same tensor section, using the original equation to degree d. -/
irreducible_def divisorChartTensorNumerator (d : ℕ)
    (s : Γ(tensorPower (divisorLineBundle I hI) d, U.1)) : Γ(X, U) :=
  divisorNumerator (hI.pow d) U (a ^ d) (ha.pow d)
    (divisorChart_power_equation U a he d)
    ((divisorLineBundlePowerIso hI d).hom.app U.1 s)

/-- Multiplication by exactly a^d clears the denominator of the retained tensor section. -/
theorem divisorChartTensorNumerator_smul (d : ℕ)
    (s : Γ(tensorPower (divisorLineBundle I hI) d, U.1)) :
    a ^ d • s = divisorChartTensorNumerator hI U a ha he d s •
      tensorPowerSection (divisorLineBundle I hI) U.1 (divisorSection hI U.1) d := by
  apply (ConcreteCategory.bijective_of_isIso
    ((divisorLineBundlePowerIso hI d).hom.app U.1)).injective
  rw [Hom.app_smul, Hom.app_smul, divisorSection_power,
    divisorChartTensorNumerator_def]
  exact divisorNumerator_smul (hI.pow d) U (a ^ d) (ha.pow d)
    (divisorChart_power_equation U a he d) _

end FLT.Mazur.FCurve
