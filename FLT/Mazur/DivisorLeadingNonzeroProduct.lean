/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorLeadingRestriction
public import FLT.Mazur.SectionGradedNonzeroProduct
public import FLT.Mazur.SectionDivisors

/-!
# Nonzero products of leading restrictions at an actual marked point

A nonzero leading class is exactly a nonzero restriction of the original
section. On a rational Cartier point, multiplication of such restrictions
is nonzero. The ambient curve need not be integral.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {k : Type} [Field k] {X : Scheme} (f : X ⟶ Spec (.of k))
  {I : X.IdealSheafData} (hI : EffectiveCartier I)

/-- Nonzero leading classes are precisely nonzero restrictions of their original sections. -/
theorem divisorPowerLeadingClass_ne_zero_iff_restriction (m : ℕ)
    (x : ModuleScalarH f (tensorPower (divisorLineBundle I hI) (m + 1)) 0) :
    divisorPowerLeadingClass f hI m x ≠ 0 ↔
      pullGlobal I.subschemeι _ (moduleScalarH0Equiv f _ x) ≠ 0 := by
  have he : divisorPowerLeadingClass f hI m x = 0 ↔
      divisorPowerRestrictedLeading f hI m x = 0 := by
    change _ ↔ divisorLeadingRestrictionEquiv f hI m
      (divisorPowerLeadingClass f hI m x) = 0
    rw [LinearEquiv.map_eq_zero_iff]
  have hr : divisorPowerRestrictedLeading f hI m x = 0 ↔
      pullGlobal I.subschemeι _ (moduleScalarH0Equiv f _ x) = 0 := by
    rw [← divisorPowerRestrictedLeading_pullGlobal f hI m x]
    change _ ↔ moduleH0Equiv _ _ = 0
    rw [LinearEquiv.map_eq_zero_iff]
  exact not_congr (he.trans hr)

/-- On an integral point divisor, exact leading restrictions have nonzero product. -/
theorem divisorLeading_product_restriction_ne_zero
    [IsIntegral I.subscheme] [Subsingleton I.subscheme]
    (m n : ℕ)
    (x : ModuleScalarH f (tensorPower (divisorLineBundle I hI) (m + 1)) 0)
    (y : ModuleScalarH f (tensorPower (divisorLineBundle I hI) (n + 1)) 0)
    (hx : divisorPowerLeadingClass f hI m x ≠ 0)
    (hy : divisorPowerLeadingClass f hI n y ≠ 0) :
    pullGlobal I.subschemeι _ (SectionGradedMultiplication.mul (divisorLineBundle I hI)
      ⊤ (m + 1) (n + 1) (moduleScalarH0Equiv f _ x) (moduleScalarH0Equiv f _ y)) ≠ 0 :=
  SectionGradedCoordinates.pullGlobal_mul_ne_zero I.subschemeι
    hI.divisorLineBundle_locallyFreeRankOne (m + 1) (n + 1) _ _
      ((divisorPowerLeadingClass_ne_zero_iff_restriction f hI m x).mp hx)
      ((divisorPowerLeadingClass_ne_zero_iff_restriction f hI n y).mp hy)

/-- A rational marked Cartier point supplies the integral one-point fiber intrinsically. -/
theorem markedPointLeading_product_restriction_ne_zero [IsSeparated f]
    (p : Spec (.of k) ⟶ X) (hp : p ≫ f = 𝟙 _) (hP : EffectiveCartier p.ker)
    (m n : ℕ)
    (x : ModuleScalarH f (tensorPower (divisorLineBundle p.ker hP) (m + 1)) 0)
    (y : ModuleScalarH f (tensorPower (divisorLineBundle p.ker hP) (n + 1)) 0)
    (hx : divisorPowerLeadingClass f hP m x ≠ 0)
    (hy : divisorPowerLeadingClass f hP n y ≠ 0) :
    pullGlobal p.ker.subschemeι _ (SectionGradedMultiplication.mul (divisorLineBundle p.ker hP)
      ⊤ (m + 1) (n + 1) (moduleScalarH0Equiv f _ x) (moduleScalarH0Equiv f _ y)) ≠ 0 := by
  let e := sectionImageIso f p hp
  let _ : IsIntegral p.ker.subscheme := IsIntegral.of_isIso e.inv
  let _ : Subsingleton p.ker.subscheme := (Scheme.homeoOfIso e).injective.subsingleton
  exact divisorLeading_product_restriction_ne_zero f hP m n x y hx hy

end FLT.Mazur.FCurve
