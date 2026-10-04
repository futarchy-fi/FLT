/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexNonzeroTwistVanishing
public import FLT.PadicHodgeTheory.ComplexAxFixedScalars
public import FLT.PadicHodgeTheory.ComplexIntegerGradedGalois

/-! # Invariants of the actual integer de Rham graded pieces -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The fixed subspace of every nonzero actual integer graded piece is zero. -/
theorem complexDeRhamIntegerGraded_fixed_eq_zero (n : ℤ) (hn : n ≠ 0)
    (x : ComplexDeRhamIntegerGradedPiece p n)
    (hx : ∀ σ : PadicGalois p, complexDeRhamIntegerGradedGalois p σ n x = x) : x = 0 := by
  apply (complexDeRhamIntegerGradedCoordinate p n).injective
  rw [map_zero]
  apply complexTwist_fixed_eq_zero p n hn
  intro σ
  have he := complexDeRhamIntegerGradedCoordinate_galois p σ n x
  rw [hx σ] at he
  have hw : (padicCyclotomicWeight p σ n : ℂ_[p]) =
      algebraMap ℚ_[p] ℂ_[p]
        ((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv).val : ℚ_[p]) ^ n := by
    change algebraMap ℚ_[p] ℂ_[p] _ = _
    rw [map_zpow₀]
  rw [hw]
  exact he.symm

/-- In degree zero, invariants have unique coordinates in the original Q_p image. -/
theorem complexDeRhamIntegerGraded_zero_fixed_existsUnique_scalar
    (x : ComplexDeRhamIntegerGradedPiece p 0)
    (hx : ∀ σ : PadicGalois p, complexDeRhamIntegerGradedGalois p σ 0 x = x) :
    ∃! a : ℚ_[p], algebraMap ℚ_[p] ℂ_[p] a = complexDeRhamIntegerGradedCoordinate p 0 x := by
  apply complexGalois_fixed_existsUnique_scalar p
  intro σ
  have he := complexDeRhamIntegerGradedCoordinate_galois p σ 0 x
  rw [hx σ, zpow_zero, one_mul] at he
  exact he.symm

/-- The fixed vectors of the actual degree-zero quotient are exactly the scalar coordinates. -/
theorem complexDeRhamIntegerGraded_zero_fixed_iff
    (x : ComplexDeRhamIntegerGradedPiece p 0) :
    (∀ σ : PadicGalois p, complexDeRhamIntegerGradedGalois p σ 0 x = x) ↔
      complexDeRhamIntegerGradedCoordinate p 0 x ∈ Set.range (algebraMap ℚ_[p] ℂ_[p]) := by
  constructor
  · intro hx
    obtain ⟨a, ha, _⟩ := complexDeRhamIntegerGraded_zero_fixed_existsUnique_scalar p x hx
    exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩ σ
    apply (complexDeRhamIntegerGradedCoordinate p 0).injective
    rw [complexDeRhamIntegerGradedCoordinate_galois, zpow_zero, one_mul, ← ha,
      complexGalois_algebraMap]

end PadicHodgeTheory
