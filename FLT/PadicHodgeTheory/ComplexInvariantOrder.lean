/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexIntegerGradedInvariants

/-! # Nonzero invariants in the original de Rham field have order zero -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- An invariant field representative gives an invariant class in the actual graded quotient. -/
theorem complexDeRhamIntegerGradedRepresentative_fixed (n : ℤ)
    (a : ComplexBDeRhamPlus p)
    (ha : ∀ σ : PadicGalois p,
      σ • (fractionalPrincipalEquiv (K := ComplexBDeRham p)
        (complexCyclotomicLog_ne_zero p) n a : ComplexBDeRham p) =
      (fractionalPrincipalEquiv (K := ComplexBDeRham p)
        (complexCyclotomicLog_ne_zero p) n a : ComplexBDeRham p)) :
    ∀ σ : PadicGalois p, complexDeRhamIntegerGradedGalois p σ n
      (complexDeRhamIntegerGradedRepresentative p n a) =
      complexDeRhamIntegerGradedRepresentative p n a := by
  intro σ
  change Submodule.Quotient.mk (complexDeRhamIntegerFiltrationGalois p σ n
    (fractionalPrincipalEquiv (K := ComplexBDeRham p) (complexCyclotomicLog_ne_zero p) n a)) = _
  congr 1
  exact Subtype.ext (ha σ)

/-- A unit coefficient of an invariant integer-power representative forces exponent zero. -/
theorem complexDeRham_fixed_unit_exponent_eq_zero (n : ℤ) (u : (ComplexBDeRhamPlus p)ˣ)
    (hu : ∀ σ : PadicGalois p,
      σ • (algebraMap (ComplexBDeRhamPlus p) (ComplexBDeRham p) (u : ComplexBDeRhamPlus p) *
        (algebraMap (ComplexBDeRhamPlus p) (ComplexBDeRham p)
          (complexCyclotomicLog p)) ^ n) =
      algebraMap (ComplexBDeRhamPlus p) (ComplexBDeRham p) (u : ComplexBDeRhamPlus p) *
        (algebraMap (ComplexBDeRhamPlus p) (ComplexBDeRham p)
          (complexCyclotomicLog p)) ^ n) : n = 0 := by
  by_contra hn
  have hf := complexDeRhamIntegerGradedRepresentative_fixed p n (u : ComplexBDeRhamPlus p)
    (by simpa only [fractionalPrincipalEquiv_coe] using hu)
  have hz := complexDeRhamIntegerGraded_fixed_eq_zero p n hn _ hf
  have ht := congrArg (complexDeRhamIntegerGradedCoordinate p n) hz
  rw [complexDeRhamIntegerGradedCoordinate_representative, map_zero] at ht
  exact (u.isUnit.map (complexDeRhamTheta p)).ne_zero ht

/-- Every nonzero fixed element lies in B_dR^+ with a unit coefficient: its order is zero. -/
theorem complexDeRham_fixed_exists_unit {x : ComplexBDeRham p} (hx : x ≠ 0)
    (hfix : ∀ σ : PadicGalois p, σ • x = x) :
    ∃ u : (ComplexBDeRhamPlus p)ˣ,
      algebraMap (ComplexBDeRhamPlus p) (ComplexBDeRham p) (u : ComplexBDeRhamPlus p) = x := by
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
    (complexCyclotomicLog_irreducible p) hx
  have he : x = algebraMap (ComplexBDeRhamPlus p) (ComplexBDeRham p)
      (u : ComplexBDeRhamPlus p) *
        (algebraMap (ComplexBDeRhamPlus p) (ComplexBDeRham p) (complexCyclotomicLog p)) ^ n := by
    simpa only [Units.smul_def, Algebra.smul_def] using hu
  have hn := complexDeRham_fixed_unit_exponent_eq_zero p n u (by simpa only [← he] using hfix)
  refine ⟨u, ?_⟩
  simpa only [hn, zpow_zero, mul_one] using he.symm

/-- Every invariant of the original field has an integral representative. -/
theorem complexDeRham_fixed_exists_integral (x : ComplexBDeRham p)
    (hx : ∀ σ : PadicGalois p, σ • x = x) :
    ∃ a : ComplexBDeRhamPlus p, algebraMap (ComplexBDeRhamPlus p) (ComplexBDeRham p) a = x := by
  by_cases hz : x = 0
  · exact ⟨0, by simp [hz]⟩
  obtain ⟨u, hu⟩ := complexDeRham_fixed_exists_unit p hz hx
  exact ⟨u, hu⟩

end PadicHodgeTheory
