/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexIntegerGraded
public import FLT.PadicHodgeTheory.ComplexDeRhamFieldGalois

/-! # The original field action preserves every integer de Rham filtration level -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The action on an actual a*t^n representative uses the original character in Q_p. -/
theorem complexDeRhamIntegerFiltration_galois_coefficient (σ : PadicGalois p) (n : ℤ)
    (a : ComplexBDeRhamPlus p) :
    σ • (fractionalPrincipalEquiv (K := ComplexBDeRham p)
      (complexCyclotomicLog_ne_zero p) n a : ComplexBDeRham p) =
      (fractionalPrincipalEquiv (K := ComplexBDeRham p) (complexCyclotomicLog_ne_zero p) n
        (complexDeRhamGalois p σ a * complexPadicToDeRham p
          (((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv).val : ℚ_[p]) ^ n)) :
            ComplexBDeRham p) := by
  rw [fractionalPrincipalEquiv_coe, fractionalPrincipalEquiv_coe]
  change σ • (algebraMap (ComplexBDeRhamPlus p) (ComplexBDeRham p) a *
    complexCyclotomicFieldPeriod p ^ n) = _
  rw [smul_mul', complexDeRhamField_smul_algebraMap,
    complexCyclotomicFieldPeriod_zpow_smul, map_mul]
  change _ = algebraMap (ComplexBDeRhamPlus p) (ComplexBDeRham p) (complexDeRhamGalois p σ a) *
    complexPadicToDeRhamField p _ * complexCyclotomicFieldPeriod p ^ n
  rw [map_zpow₀, mul_assoc]

/-- Stability holds at every integer level, with the original field action. -/
theorem complexDeRhamIntegerFiltration_galois_mem (σ : PadicGalois p) (n : ℤ)
    {x : ComplexBDeRham p} (hx : x ∈ ComplexDeRhamIntegerFiltration p n) :
    σ • x ∈ ComplexDeRhamIntegerFiltration p n := by
  obtain ⟨a, ha⟩ := (fractionalPrincipalEquiv (K := ComplexBDeRham p)
    (complexCyclotomicLog_ne_zero p) n).surjective ⟨x, hx⟩
  have he : (fractionalPrincipalEquiv (K := ComplexBDeRham p)
      (complexCyclotomicLog_ne_zero p) n a : ComplexBDeRham p) = x :=
    congrArg Subtype.val ha
  rw [← he, complexDeRhamIntegerFiltration_galois_coefficient]
  exact Subtype.property _

/-- Restrict the actual field action to each integer filtration submodule. -/
def complexDeRhamIntegerFiltrationGalois (σ : PadicGalois p) (n : ℤ) :
    ComplexDeRhamIntegerFiltration p n →+ ComplexDeRhamIntegerFiltration p n where
  toFun x := ⟨σ • (x : ComplexBDeRham p),
    complexDeRhamIntegerFiltration_galois_mem p σ n x.property⟩
  map_zero' := Subtype.ext (smul_zero σ)
  map_add' x y := Subtype.ext (smul_add σ (x : ComplexBDeRham p) y)

/-- The restricted map retains the coefficient formula. -/
theorem complexDeRhamIntegerFiltrationGalois_coefficient (σ : PadicGalois p) (n : ℤ)
    (a : ComplexBDeRhamPlus p) :
    complexDeRhamIntegerFiltrationGalois p σ n
      (fractionalPrincipalEquiv (K := ComplexBDeRham p) (complexCyclotomicLog_ne_zero p) n a) =
      fractionalPrincipalEquiv (K := ComplexBDeRham p) (complexCyclotomicLog_ne_zero p) n
        (complexDeRhamGalois p σ a * complexPadicToDeRham p
          (((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv).val : ℚ_[p]) ^ n)) :=
  Subtype.ext (complexDeRhamIntegerFiltration_galois_coefficient p σ n a)

end PadicHodgeTheory
