/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicIdealPowerComparison
public import FLT.Mazur.AdicLinearReductionProperty

/-!
# Original reduced equations from full rank-ideal approximations

The ambient equation ring includes every coordinate of the original operator.
Whole scalar-fiber support and finite generation convert its rank errors into
solutions of the original scalar reductions. No flatness of reduction is used.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.AdicLinearImageDescent
variable {R A B : Type*} [CommRing R] [AddCommGroup A] [Module R A]
  [CommRing B] [Algebra R B] (F : A →ₗ[R] B) (J : Ideal R) (K : Ideal B)

/-- Full rank equations construct solutions of the actual original scalar reductions. -/
theorem reduced_solutions_of_rank_errors (hK : K.FG)
    (hsupport : PrimeSpectrum.zeroLocus (J.map (algebraMap R B) : Set B) ⊆
      PrimeSpectrum.zeroLocus (K : Set B)) (x : B)
    (h : ∀ k : ℕ, ∃ v : A, x - F v ∈ K ^ (k + 1)) :
    HasReducedSolutions F J x := by
  apply (hasReducedSolutions_iff F J x).mpr
  intro n
  apply (exists_reduced_solution_iff F J (n + 1) x).mpr
  exact AdicIdealPowerComparison.scalar_approximations J K F x hK
    ((PrimeSpectrum.zeroLocus_subset_zeroLocus_iff _ _).mp hsupport) h n

variable [IsNoetherianRing R] [Module.Finite R (B ⧸ LinearMap.range F)]

/-- Original finite cokernel descends the full rank approximations to a nonvanishing numerator. -/
theorem scaled_solution_of_rank_errors (hK : K.FG)
    (hsupport : PrimeSpectrum.zeroLocus (J.map (algebraMap R B) : Set B) ⊆
      PrimeSpectrum.zeroLocus (K : Set B)) (P : Ideal R) (hJP : J ≤ P)
    (hP : P ≠ ⊤) (x : B) (h : ∀ k : ℕ, ∃ v : A, x - F v ∈ K ^ (k + 1)) :
    ∃ s : R, s ∉ P ∧ 1 - s ∈ J ∧ ∃ v : A, F v = s • x := by
  apply exists_scaled_solution_of_reductions F J P hJP hP x
  exact (hasReducedSolutions_iff F J x).mp
    (reduced_solutions_of_rank_errors F J K hK hsupport x h)

/-- Local original scalars recover an unscaled solution of the full original operator. -/
theorem local_solution_of_rank_errors [IsLocalRing R] (hJ : J ≠ ⊤) (hK : K.FG)
    (hsupport : PrimeSpectrum.zeroLocus (J.map (algebraMap R B) : Set B) ⊆
      PrimeSpectrum.zeroLocus (K : Set B)) (x : B)
    (h : ∀ k : ℕ, ∃ v : A, x - F v ∈ K ^ (k + 1)) : ∃ v : A, F v = x := by
  apply exists_solution_of_local_reductions F J hJ x
  exact (hasReducedSolutions_iff F J x).mp
    (reduced_solutions_of_rank_errors F J K hK hsupport x h)

end FLT.Mazur.AdicLinearImageDescent
