/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationShear
public import FLT.Mazur.WeierstrassModificationXShear
public import FLT.Mazur.WeierstrassDilatationBaseChange
public import FLT.Mazur.WeierstrassModificationXBaseChangeGenerators

/-!
# Actual coefficient extension followed by the integral shear

Identify both original tensor chart algebras with the coefficient-extended
sheared equations. Pure-tensor formulas retain the original coefficient maps.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (S : Type*) [CommRing S] [Algebra R S] (r : S)
local notation "V" => W.map (algebraMap R S)
local notation "U" => rootShearCurve V r
local notation "q" => algebraMap R S

/-- The actual divided tensor chart is the coefficient-extended sheared equation. -/
def dividedCoefficientShearEquiv :
    WeierstrassDilatation.ScalarExtension W s b3 b4 b6 S ≃ₐ[S]
      WeierstrassDilatation.Coordinate U (q s) (q b3) (q b4 - r * q b3) (q b6) :=
  (WeierstrassDilatation.baseChangeEquiv W s b3 b4 b6 S).trans
    (WeierstrassDilatation.shearEquiv V (q s) (q b3) (q b4) (q b6) r)

/-- Every original divided pure tensor retains its coefficient projection under shearing. -/
theorem dividedCoefficientShearEquiv_tmul
    (a : S) (z : WeierstrassDilatation.Coordinate W s b3 b4 b6) :
    dividedCoefficientShearEquiv W s b3 b4 b6 S r (a ⊗ₜ[R] z) =
      a • WeierstrassDilatation.shearForward V (q s) (q b3) (q b4) (q b6) r
        (WeierstrassDilatation.coefficientMap W s b3 b4 b6 S z) := by
  change WeierstrassDilatation.shearForward V (q s) (q b3) (q b4) (q b6) r
    (WeierstrassDilatation.baseChangeForward W s b3 b4 b6 S (a ⊗ₜ[R] z)) = _
  rw [WeierstrassDilatation.baseChangeForward_tmul, map_smul]

/-- The original incidence tensor chart is the actual coefficient-extended sheared chart. -/
def incidenceCoefficientShearEquiv :
    WeierstrassModificationX.ScalarExtension W s b3 b4 b6 S ≃ₐ[S]
      WeierstrassModificationX.Coordinate U (q s) (q b3) (q b4 - r * q b3) (q b6) :=
  (WeierstrassModificationX.baseChangeEquiv W s b3 b4 b6 S).trans
    (WeierstrassModificationX.shearEquiv V (q s) (q b3) (q b4) (q b6) r)

/-- Every incidence tensor retains its original coefficient projection, including the conic. -/
theorem incidenceCoefficientShearEquiv_tmul
    (a : S) (z : WeierstrassModificationX.Coordinate W s b3 b4 b6) :
    incidenceCoefficientShearEquiv W s b3 b4 b6 S r (a ⊗ₜ[R] z) =
      a • WeierstrassModificationX.shearForward V (q s) (q b3) (q b4) (q b6) r
        (WeierstrassModificationX.coefficientMap W s b3 b4 b6 S z) := by
  change WeierstrassModificationX.shearForward V (q s) (q b3) (q b4) (q b6) r
    (WeierstrassModificationX.baseChangeForward W s b3 b4 b6 S (a ⊗ₜ[R] z)) = _
  rw [WeierstrassModificationX.baseChangeForward_tmul, map_smul]

/-- The original incidence parameter is fixed by the full coefficient/shear comparison. -/
theorem incidenceCoefficientShearEquiv_t :
    incidenceCoefficientShearEquiv W s b3 b4 b6 S r
        ((1 : S) ⊗ₜ[R] WeierstrassModificationX.t W s b3 b4 b6) =
      WeierstrassModificationX.t U (q s) (q b3) (q b4 - r * q b3) (q b6) := by
  rw [incidenceCoefficientShearEquiv_tmul, one_smul,
    WeierstrassModificationX.coefficientMap_t, WeierstrassModificationX.shearForward_t]

/-- The original slope becomes the sheared slope plus the actual integral root. -/
theorem incidenceCoefficientShearEquiv_v :
    incidenceCoefficientShearEquiv W s b3 b4 b6 S r
        ((1 : S) ⊗ₜ[R] WeierstrassModificationX.v W s b3 b4 b6) =
      WeierstrassModificationX.v U (q s) (q b3) (q b4 - r * q b3) (q b6) +
        algebraMap S _ r := by
  rw [incidenceCoefficientShearEquiv_tmul, one_smul,
    WeierstrassModificationX.coefficientMap_v, WeierstrassModificationX.shearForward_v]

end FLT.Mazur.WeierstrassDividedDepth
