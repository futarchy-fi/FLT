/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexDeRhamFractionField
public import FLT.PadicHodgeTheory.ComplexCyclotomicLogCharacter
public import FLT.PadicHodgeTheory.ComplexPadicScalarAction

/-! # The actual Galois action and fixed scalars in the de Rham field -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- Extend the already constructed action to the actual fraction field. -/
instance instMulSemiringActionComplexBDeRham :
    MulSemiringAction (PadicGalois p) (ComplexBDeRham p) :=
  IsFractionRing.mulSemiringAction (PadicGalois p) (ComplexBDeRhamPlus p) (ComplexBDeRham p)

/-- The period-field action agrees with the original completed-ring action. -/
theorem complexDeRhamField_smul_algebraMap (σ : PadicGalois p) (x : ComplexBDeRhamPlus p) :
    σ • algebraMap (ComplexBDeRhamPlus p) (ComplexBDeRham p) x =
      algebraMap (ComplexBDeRhamPlus p) (ComplexBDeRham p) (complexDeRhamGalois p σ x) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap (complexDeRhamGaloisEquiv p σ) x

/-- The actual Q_p embedding in the period field. -/
def complexPadicToDeRhamField : ℚ_[p] →+* ComplexBDeRham p :=
  (algebraMap (ComplexBDeRhamPlus p) (ComplexBDeRham p)).comp (complexPadicToDeRham p)

/-- The existing scalar embedding remains injective in the period field. -/
theorem complexPadicToDeRhamField_injective : Function.Injective (complexPadicToDeRhamField p) :=
  (complexPadicToDeRhamField p).injective

/-- Q_p lies in the fixed field; this is only the forward inclusion. -/
theorem complexPadicToDeRhamField_fixed (σ : PadicGalois p) (x : ℚ_[p]) :
    σ • complexPadicToDeRhamField p x = complexPadicToDeRhamField p x := by
  change σ • algebraMap (ComplexBDeRhamPlus p) (ComplexBDeRham p) (complexPadicToDeRham p x) = _
  rw [complexDeRhamField_smul_algebraMap, complexPadicToDeRham_galois]
  rfl

/-- The original logarithmic period viewed in the actual field. -/
def complexCyclotomicFieldPeriod : ComplexBDeRham p :=
  algebraMap (ComplexBDeRhamPlus p) (ComplexBDeRham p) (complexCyclotomicLog p)

/-- The field period has the actual cyclotomic character. -/
theorem complexCyclotomicFieldPeriod_smul (σ : PadicGalois p) :
    σ • complexCyclotomicFieldPeriod p =
      complexPadicToDeRhamField p
        ((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv).val : ℚ_[p]) *
          complexCyclotomicFieldPeriod p := by
  rw [complexCyclotomicFieldPeriod, complexDeRhamField_smul_algebraMap,
    complexCyclotomicLog_galois_character, map_mul]
  rfl

/-- Every integer power, including negative powers, transforms with its cyclotomic weight. -/
theorem complexCyclotomicFieldPeriod_zpow_smul (σ : PadicGalois p) (n : ℤ) :
    σ • complexCyclotomicFieldPeriod p ^ n =
      complexPadicToDeRhamField p
        ((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv).val : ℚ_[p]) ^ n *
          complexCyclotomicFieldPeriod p ^ n := by
  change (MulSemiringAction.toRingEquiv (PadicGalois p) (ComplexBDeRham p) σ)
    (complexCyclotomicFieldPeriod p ^ n) = _
  rw [map_zpow₀]
  change (σ • complexCyclotomicFieldPeriod p) ^ n = _
  rw [complexCyclotomicFieldPeriod_smul, mul_zpow]

end PadicHodgeTheory
