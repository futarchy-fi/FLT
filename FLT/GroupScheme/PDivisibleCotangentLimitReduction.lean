/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleCotangentExactness
public import FLT.GroupScheme.PDivisibleCotangentSurjective
public import Mathlib.Order.KonigLemma

/-! # Reduction of the actual cotangent inverse limit -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height) [∀ n, Finite (X.LevelCotangent n)]

/-- A limit vector vanishing at level m admits one coherent p^m division in the same limit. -/
theorem cotangentEval_eq_zero_iff (m : ℕ) (x : X.cotangentLimit) :
    X.cotangentEval m x = 0 ↔ ∃ y : X.cotangentLimit, p ^ m • y = x := by
  constructor
  · intro hx
    let F (k : ℕ) := {a : X.LevelCotangent k // p ^ m • a = X.cotangentEval k x}
    have (k : ℕ) : Nonempty (F k) := by
      have hz : X.cotangentRestriction (Nat.le_add_right m k)
          (X.cotangentEval (m + k) x) = 0 := (X.cotangentEval_restriction _ x).trans hx
      obtain ⟨a, ha⟩ := (X.cotangentRestriction_eq_zero_iff _ _).mp hz
      refine ⟨X.cotangentRestriction (Nat.le_add_left k m) a, ?_⟩
      rw [← map_nsmul, ha, X.cotangentEval_restriction]
    let π {i j : ℕ} (h : i ≤ j) (a : F j) : F i :=
      ⟨X.cotangentRestriction h a.val, by
        rw [← map_nsmul, a.property, X.cotangentEval_restriction]⟩
    obtain ⟨f, hf⟩ := exists_seq_forall_proj_of_forall_finite π
      (by intro i a; apply Subtype.ext; change X.cotangentRestriction _ a.val = a.val
          rw [X.cotangentRestriction_refl]; rfl)
      (by intro i j k h h' a; apply Subtype.ext
          exact LinearMap.congr_fun (X.cotangentRestriction_comp h h') a.val)
      (fun _ _ ↦ Set.toFinite _)
    refine ⟨⟨fun k ↦ (f k).val, fun h ↦ congrArg Subtype.val (hf h)⟩, ?_⟩
    apply X.cotangentLimit_ext
    intro k
    exact (f k).property
  · rintro ⟨y, rfl⟩
    rw [map_nsmul]
    exact X.cotangent_pow_smul_eq_zero m _

/-- The actual evaluation kernel is precisely the submodule of p-power multiples. -/
theorem cotangentEval_ker (m : ℕ) :
    LinearMap.ker (X.cotangentEval m) =
      LinearMap.range (p ^ m • (LinearMap.id : X.cotangentLimit →ₗ[R] _)) := by
  ext x
  exact X.cotangentEval_eq_zero_iff m x

/-- Reduction of the original limit is the original level cotangent, with its original scalars. -/
def cotangentReductionEquiv (m : ℕ) :
    (X.cotangentLimit ⧸
      LinearMap.range (p ^ m • (LinearMap.id : X.cotangentLimit →ₗ[R] _))) ≃ₗ[R]
      X.LevelCotangent m :=
  (Submodule.quotEquivOfEq _ _ (X.cotangentEval_ker m).symm).trans
    ((X.cotangentEval m).quotKerEquivOfSurjective (X.cotangentEval_surjective m))

/-- The reduction equivalence is induced by the specified original evaluation. -/
theorem cotangentReductionEquiv_mk (m : ℕ) (x : X.cotangentLimit) :
    X.cotangentReductionEquiv m (Submodule.Quotient.mk x) = X.cotangentEval m x := rfl

end ThreeAdicPlan.PDivisibleSystem
