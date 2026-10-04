/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.PadicCyclotomicRelativeMinpoly
public import FLT.PadicHodgeTheory.PadicRelativeGalois

/-! # Actual relative automorphisms with prescribed cyclotomic root action -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The binomial minimal polynomial supplies an automorphism with exponent 1+p^(n+1). -/
theorem padicCyclotomic_exists_tail_automorphism (n r : ℕ) (ζ : PadicAlgCl p)
    (hζ : IsPrimitiveRoot ζ (p ^ (n + r + 1))) :
    ∃ σ : Gal(PadicAlgCl p/padicCyclotomicTower p (n + 1)),
      σ ζ = ζ ^ (1 + p ^ (n + 1)) := by
  have he : (ζ ^ (1 + p ^ (n + 1))) ^ (p ^ r) = ζ ^ (p ^ r) := by
    have hp : p ^ (n + 1) * p ^ r = p ^ (n + r + 1) := by
      rw [← pow_add]; congr 1; omega
    rw [← pow_mul, Nat.add_mul, one_mul, hp, pow_add, hζ.pow_eq_one, mul_one]
  obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root'
    (Algebra.IsIntegral.isIntegral (R := padicCyclotomicTower p (n + 1)) ζ).isAlgebraic
    (show Polynomial.aeval (ζ ^ (1 + p ^ (n + 1)))
      (minpoly (padicCyclotomicTower p (n + 1)) ζ) = 0 by
      rw [padicCyclotomicRelative_minpoly p n r ζ hζ]
      simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
        IntermediateField.algebraMap_apply, he, sub_self])
  exact ⟨σ, hσ⟩

end PadicHodgeTheory
