/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleCotangentLimitReduction
public import FLT.GroupScheme.FiniteFlatTangentNaturality

/-! # Torsion-valued tangent functionals on the actual cotangent limit -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K M : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  [AddCommGroup M] [Module R M] (X : PDivisibleSystem R K p height)

/-- Precomposition with the original evaluation, with arbitrary coefficient module. -/
def cotangentEvalPrecomp (n : ℕ) :
    (X.LevelCotangent n →ₗ[R] M) →ₗ[R] (X.cotangentLimit →ₗ[R] M) :=
  (LinearMap.llcomp R X.cotangentLimit (X.LevelCotangent n) M).flip (X.cotangentEval n)

/-- No functional is lost by pullback to the actual cotangent limit. -/
theorem cotangentEvalPrecomp_injective (n : ℕ) :
    Function.Injective (X.cotangentEvalPrecomp (M := M) n) :=
  (X.cotangentEval_surjective n).injective_linearMapComp_right

variable [∀ n, Finite (X.LevelCotangent n)]

/-- Every torsion-valued limit functional descends to the corresponding original level. -/
theorem cotangentEvalPrecomp_surjective (n : ℕ) (hM : ∀ a : M, p ^ n • a = 0) :
    Function.Surjective (X.cotangentEvalPrecomp (M := M) n) := by
  intro f
  let e := (X.cotangentEval n).quotKerEquivOfSurjective (X.cotangentEval_surjective n)
  let d := (LinearMap.ker (X.cotangentEval n)).liftQ f (by
    intro x hx
    obtain ⟨y, rfl⟩ := (X.cotangentEval_eq_zero_iff n x).mp hx
    change f (p ^ n • y) = 0
    rw [map_nsmul, hM])
  refine ⟨d.comp e.symm.toLinearMap, ?_⟩
  ext x
  change d (e.symm (X.cotangentEval n x)) = f x
  have he : e (Submodule.Quotient.mk x) = X.cotangentEval n x := rfl
  rw [← he, e.symm_apply_apply]
  rfl

/-- Linear functionals on the actual level and limit agree for p^n-torsion coefficients. -/
def cotangentTorsionEquiv (n : ℕ) (hM : ∀ a : M, p ^ n • a = 0) :
    (X.LevelCotangent n →ₗ[R] M) ≃ₗ[R] (X.cotangentLimit →ₗ[R] M) :=
  LinearEquiv.ofBijective (X.cotangentEvalPrecomp n)
    ⟨X.cotangentEvalPrecomp_injective n, X.cotangentEvalPrecomp_surjective n hM⟩

/-- This equivalence is the prescribed evaluation pullback. -/
theorem cotangentTorsionEquiv_apply (n : ℕ) (hM : ∀ a : M, p ^ n • a = 0)
    (f : X.LevelCotangent n →ₗ[R] M) (x : X.cotangentLimit) :
    X.cotangentTorsionEquiv n hM f x = f (X.cotangentEval n x) := rfl

/-- Actual finite-level Leibniz functionals correspond to torsion-valued limit functionals. -/
def tangentTorsionEquiv (n : ℕ) (hM : ∀ a : M, p ^ n • a = 0) :
    (X.level n).Tangent (M := M) ≃ₗ[R] (X.cotangentLimit →ₗ[R] M) :=
  (X.level n).cotangentTangentEquiv.symm.trans (X.cotangentTorsionEquiv n hM)

end ThreeAdicPlan.PDivisibleSystem
