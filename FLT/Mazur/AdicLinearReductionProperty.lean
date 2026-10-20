/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicLinearReductionLifts

/-!
# A sealed property of solutions on every original reduction

Keeping the dependent quotient expressions behind a proved predicate allows
geometric callers to use reduced solutions without expanding all reductions.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.AdicLinearImageDescent
variable {R A M : Type*} [CommRing R] [AddCommGroup A] [Module R A]
  [AddCommGroup M] [Module R M] (F : A →ₗ[R] M) (I : Ideal R)

/-- Every positive scalar reduction of the original equation has a solution. -/
@[irreducible]
def HasReducedSolutions (x : M) : Prop :=
  ∀ n : ℕ, ∃ v, reduction F I (n + 1) v =
    (I ^ (n + 1) • (⊤ : Submodule R M)).mkQ x

/-- The sealed property retains the exact original reduced equations. -/
theorem hasReducedSolutions_iff (x : M) : HasReducedSolutions F I x ↔
    ∀ n : ℕ, ∃ v, reduction F I (n + 1) v =
      (I ^ (n + 1) • (⊤ : Submodule R M)).mkQ x := by
  unfold HasReducedSolutions
  rfl

/-- Reduced solutions construct the original full equation approximations. -/
theorem approximations_of_reduced_solutions (x : M) (h : HasReducedSolutions F I x) :
    ∀ n : ℕ, ∃ v : A, x - F v ∈ I ^ (n + 1) • (⊤ : Submodule R M) :=
  fun n ↦ (exists_reduced_solution_iff F I (n + 1) x).mp
    ((hasReducedSolutions_iff F I x).mp h n)

end FLT.Mazur.AdicLinearImageDescent
