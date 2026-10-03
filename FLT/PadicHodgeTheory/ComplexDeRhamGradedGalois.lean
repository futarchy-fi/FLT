/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexDeRhamGraded
public import FLT.PadicHodgeTheory.ComplexCyclotomicLogCharacter
public import FLT.PadicHodgeTheory.ComplexPadicScalarResidue

/-! # Cyclotomic twists on the actual nonnegative de Rham graded quotients -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- Stability of principal logarithm powers follows from the original filtration stability. -/
theorem complexDeRhamGalois_mem_log_power (σ : PadicGalois p) (n : ℕ)
    {x : ComplexBDeRhamPlus p} (hx : x ∈ Ideal.span {complexCyclotomicLog p ^ n}) :
    complexDeRhamGalois p σ x ∈ Ideal.span {complexCyclotomicLog p ^ n} := by
  rw [complexCyclotomicLog_filtration] at hx ⊢
  exact (complexDeRhamGalois_mem_filtration_iff p σ x n).mpr hx

/-- The existing Galois action preserves each principal power ideal. -/
def complexDeRhamPowerGalois (σ : PadicGalois p) (n : ℕ) :
    Ideal.span {complexCyclotomicLog p ^ n} →+ Ideal.span {complexCyclotomicLog p ^ n} where
  toFun x := ⟨complexDeRhamGalois p σ x, complexDeRhamGalois_mem_log_power p σ n x.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

/-- Descend the actual ideal action through the next principal power. -/
def complexDeRhamGradedGalois (σ : PadicGalois p) (n : ℕ) :
    ComplexDeRhamGradedPiece p n →+ ComplexDeRhamGradedPiece p n :=
  QuotientAddGroup.map (principalGradedSubmodule (complexCyclotomicLog p) n).toAddSubgroup
    (principalGradedSubmodule (complexCyclotomicLog p) n).toAddSubgroup
    (complexDeRhamPowerGalois p σ n) (by
      intro x hx
      change complexDeRhamGalois p σ x ∈ Ideal.span {complexCyclotomicLog p ^ (n + 1)}
      exact complexDeRhamGalois_mem_log_power p σ (n + 1) hx)

/-- On coefficient representatives, the descended map uses sigma(a) times chi(sigma)^n. -/
theorem complexDeRhamGradedGalois_representative (σ : PadicGalois p) (n : ℕ)
    (a : ComplexBDeRhamPlus p) :
    complexDeRhamGradedGalois p σ n (complexDeRhamGradedRepresentative p n a) =
      complexDeRhamGradedRepresentative p n
        (complexDeRhamGalois p σ a *
          complexPadicToDeRham p
            ((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv).val : ℚ_[p]) ^ n) := by
  change Submodule.Quotient.mk (complexDeRhamPowerGalois p σ n
    (principalPowerEquiv (complexCyclotomicLog_ne_zero p) n a)) =
      Submodule.Quotient.mk (principalPowerEquiv (complexCyclotomicLog_ne_zero p) n _)
  congr 1
  apply Subtype.ext
  change complexDeRhamGalois p σ (a * complexCyclotomicLog p ^ n) =
    (_ * _) * complexCyclotomicLog p ^ n
  rw [map_mul, map_pow, complexCyclotomicLog_galois_character, mul_pow, mul_assoc]

/-- In the canonical C_p coordinates the actual quotient action is the weight-n twist. -/
theorem complexDeRhamGradedCoordinate_galois (σ : PadicGalois p) (n : ℕ)
    (x : ComplexDeRhamGradedPiece p n) :
    complexDeRhamGradedCoordinate p n (complexDeRhamGradedGalois p σ n x) =
      algebraMap ℚ_[p] ℂ_[p]
        ((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv).val : ℚ_[p]) ^ n *
          complexGalois p σ (complexDeRhamGradedCoordinate p n x) := by
  obtain ⟨a, rfl⟩ := complexDeRhamGradedRepresentative_surjective p n x
  rw [complexDeRhamGradedGalois_representative, complexDeRhamGradedCoordinate_representative,
    complexDeRhamGradedCoordinate_representative, map_mul, map_pow,
    complexPadicToDeRham_theta, complexDeRhamTheta_equivariant, mul_comm]

/-- Identity on each actual graded quotient. -/
theorem complexDeRhamGradedGalois_one (n : ℕ) (x : ComplexDeRhamGradedPiece p n) :
    complexDeRhamGradedGalois p 1 n x = x := by
  induction x using Submodule.Quotient.induction_on with
  | H a =>
    change Submodule.Quotient.mk (complexDeRhamPowerGalois p 1 n a) =
      Submodule.Quotient.mk a
    congr 1
    exact Subtype.ext (complexDeRhamGalois_one p a)

/-- Composition on each actual graded quotient. -/
theorem complexDeRhamGradedGalois_mul (σ τ : PadicGalois p) (n : ℕ)
    (x : ComplexDeRhamGradedPiece p n) :
    complexDeRhamGradedGalois p (σ * τ) n x =
      complexDeRhamGradedGalois p σ n (complexDeRhamGradedGalois p τ n x) := by
  induction x using Submodule.Quotient.induction_on with
  | H a =>
    change Submodule.Quotient.mk (complexDeRhamPowerGalois p (σ * τ) n a) =
      Submodule.Quotient.mk (complexDeRhamPowerGalois p σ n (complexDeRhamPowerGalois p τ n a))
    congr 1
    exact Subtype.ext (complexDeRhamGalois_mul p σ τ a)

/-- The quotient maps assemble into the actual additive Galois action. -/
instance instDistribMulActionComplexDeRhamGraded (n : ℕ) :
    DistribMulAction (PadicGalois p) (ComplexDeRhamGradedPiece p n) where
  smul σ x := complexDeRhamGradedGalois p σ n x
  one_smul := complexDeRhamGradedGalois_one p n
  mul_smul σ τ := complexDeRhamGradedGalois_mul p σ τ n
  smul_zero σ := map_zero (complexDeRhamGradedGalois p σ n)
  smul_add σ := map_add (complexDeRhamGradedGalois p σ n)

end PadicHodgeTheory
