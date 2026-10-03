/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexIntegerFiltrationGalois

/-! # The actual cyclotomic twist on every integer de Rham graded quotient -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- Descend the original restricted field action through the actual next filtration level. -/
def complexDeRhamIntegerGradedGalois (σ : PadicGalois p) (n : ℤ) :
    ComplexDeRhamIntegerGradedPiece p n →+ ComplexDeRhamIntegerGradedPiece p n :=
  QuotientAddGroup.map
    (fractionalPrincipalNext (K := ComplexBDeRham p) (complexCyclotomicLog p) n).toAddSubgroup
    (fractionalPrincipalNext (K := ComplexBDeRham p) (complexCyclotomicLog p) n).toAddSubgroup
    (complexDeRhamIntegerFiltrationGalois p σ n) (by
      intro x hx
      change σ • (x : ComplexBDeRham p) ∈ ComplexDeRhamIntegerFiltration p (n + 1)
      exact complexDeRhamIntegerFiltration_galois_mem p σ (n + 1) hx)

/-- The descended action retains the coefficient formula from the original field. -/
theorem complexDeRhamIntegerGradedGalois_representative (σ : PadicGalois p) (n : ℤ)
    (a : ComplexBDeRhamPlus p) :
    complexDeRhamIntegerGradedGalois p σ n (complexDeRhamIntegerGradedRepresentative p n a) =
      complexDeRhamIntegerGradedRepresentative p n
        (complexDeRhamGalois p σ a * complexPadicToDeRham p
          (((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv).val : ℚ_[p]) ^ n)) := by
  change Submodule.Quotient.mk (complexDeRhamIntegerFiltrationGalois p σ n
    (fractionalPrincipalEquiv (K := ComplexBDeRham p) (complexCyclotomicLog_ne_zero p) n a)) = _
  rw [complexDeRhamIntegerFiltrationGalois_coefficient]
  rfl

/-- Every integer degree has the actual weight-n character in C_p coordinates. -/
theorem complexDeRhamIntegerGradedCoordinate_galois (σ : PadicGalois p) (n : ℤ)
    (x : ComplexDeRhamIntegerGradedPiece p n) :
    complexDeRhamIntegerGradedCoordinate p n (complexDeRhamIntegerGradedGalois p σ n x) =
      algebraMap ℚ_[p] ℂ_[p]
        ((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv).val : ℚ_[p]) ^ n *
          complexGalois p σ (complexDeRhamIntegerGradedCoordinate p n x) := by
  obtain ⟨a, rfl⟩ := complexDeRhamIntegerGradedRepresentative_surjective p n x
  rw [complexDeRhamIntegerGradedGalois_representative,
    complexDeRhamIntegerGradedCoordinate_representative,
    complexDeRhamIntegerGradedCoordinate_representative, map_mul,
    complexPadicToDeRham_theta, complexDeRhamTheta_equivariant, map_zpow₀, mul_comm]

/-- Identity on every actual integer graded quotient. -/
theorem complexDeRhamIntegerGradedGalois_one (n : ℤ)
    (x : ComplexDeRhamIntegerGradedPiece p n) :
    complexDeRhamIntegerGradedGalois p 1 n x = x := by
  induction x using Submodule.Quotient.induction_on with
  | H a =>
    change Submodule.Quotient.mk (complexDeRhamIntegerFiltrationGalois p 1 n a) =
      Submodule.Quotient.mk a
    congr 1
    exact Subtype.ext (one_smul (PadicGalois p) (a : ComplexBDeRham p))

/-- Composition on every actual integer graded quotient. -/
theorem complexDeRhamIntegerGradedGalois_mul (σ τ : PadicGalois p) (n : ℤ)
    (x : ComplexDeRhamIntegerGradedPiece p n) :
    complexDeRhamIntegerGradedGalois p (σ * τ) n x =
      complexDeRhamIntegerGradedGalois p σ n (complexDeRhamIntegerGradedGalois p τ n x) := by
  induction x using Submodule.Quotient.induction_on with
  | H a =>
    change Submodule.Quotient.mk (complexDeRhamIntegerFiltrationGalois p (σ * τ) n a) =
      Submodule.Quotient.mk (complexDeRhamIntegerFiltrationGalois p σ n
        (complexDeRhamIntegerFiltrationGalois p τ n a))
    congr 1
    exact Subtype.ext (mul_smul σ τ (a : ComplexBDeRham p))

/-- The actual descended maps form an additive action at every integer degree. -/
instance instDistribMulActionComplexDeRhamIntegerGraded (n : ℤ) :
    DistribMulAction (PadicGalois p) (ComplexDeRhamIntegerGradedPiece p n) where
  smul σ x := complexDeRhamIntegerGradedGalois p σ n x
  one_smul := complexDeRhamIntegerGradedGalois_one p n
  mul_smul σ τ := complexDeRhamIntegerGradedGalois_mul p σ τ n
  smul_zero σ := map_zero (complexDeRhamIntegerGradedGalois p σ n)
  smul_add σ := map_add (complexDeRhamIntegerGradedGalois p σ n)

end PadicHodgeTheory
