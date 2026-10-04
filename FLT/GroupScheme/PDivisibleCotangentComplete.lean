/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleCotangentLimitReduction
public import Mathlib.RingTheory.AdicCompletion.Basic

/-! # Adic completeness of the actual integral cotangent inverse limit -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
open scoped Pointwise
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height) [∀ n, Finite (X.LevelCotangent n)]

/-- The actual evaluation kernel is the standard p-adic filtration submodule. -/
theorem cotangentEval_ker_ideal (n : ℕ) :
    LinearMap.ker (X.cotangentEval n) =
      (Ideal.span {(p : R)}) ^ n • (⊤ : Submodule R X.cotangentLimit) := by
  ext x
  rw [LinearMap.mem_ker, X.cotangentEval_eq_zero_iff, Ideal.span_singleton_pow,
    Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp only [Submodule.mem_top, true_and, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]

/-- Congruence in the actual limit is equality at the original finite level. -/
theorem cotangent_smodEq_iff (n : ℕ) (x y : X.cotangentLimit) :
    x ≡ y [SMOD ((Ideal.span {(p : R)}) ^ n • (⊤ : Submodule R X.cotangentLimit))] ↔
      X.cotangentEval n x = X.cotangentEval n y := by
  rw [SModEq.sub_mem, ← X.cotangentEval_ker_ideal, LinearMap.mem_ker, map_sub, sub_eq_zero]

/-- The original inverse limit is complete and separated for the p-adic filtration. -/
theorem cotangentLimit_isAdicComplete :
    IsAdicComplete (Ideal.span {(p : R)}) X.cotangentLimit where
  haus' x hx := by
    apply X.cotangentLimit_ext
    intro n
    exact (X.cotangent_smodEq_iff n x 0).mp (hx n)
  prec' f hf := by
    have he {m n : ℕ} (h : m ≤ n) :
        X.cotangentEval m (f m) = X.cotangentEval m (f n) :=
      (X.cotangent_smodEq_iff m _ _).mp (hf h)
    let x : X.cotangentLimit := ⟨fun n ↦ X.cotangentEval n (f n), by
      intro m n h
      rw [X.cotangentEval_restriction, ← he h]⟩
    refine ⟨x, fun n ↦ (X.cotangent_smodEq_iff n _ _).mpr ?_⟩
    rfl

end ThreeAdicPlan.PDivisibleSystem
