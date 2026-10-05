/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleGenericExactness
public import Mathlib.Order.KonigLemma

/-! # Reduction of the actual Tate inverse limit -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)

/-- A limit vector vanishing at level m admits one coherent p^m division in the same limit. -/
theorem tateEvalLinear_eq_zero_iff (m : ℕ) (x : X.tateSequences) :
    X.tateEvalLinear m x = 0 ↔ ∃ y : X.tateSequences, p ^ m • y = x := by
  constructor
  · intro hx
    let F (k : ℕ) := {a : (X.level k).Points // p ^ m • a = X.tateEvalLinear k x}
    have (k : ℕ) : Nonempty (F k) := by
      have hz : genericHom (X.reduction (Nat.le_add_right m k))
          (X.tateEvalLinear (m + k) x) = 0 := (X.tateEval_reduction _ x).trans hx
      obtain ⟨a, ha⟩ := (X.reduction_points_eq_zero_iff _ _).mp hz
      refine ⟨genericHom (X.reduction (Nat.le_add_left k m)) a, ?_⟩
      rw [← map_nsmul, ha]
      exact X.tateEval_reduction _ x
    let π {i j : ℕ} (h : i ≤ j) (a : F j) : F i :=
      ⟨genericHom (X.reduction h) a.val, by
        rw [← map_nsmul, a.property]
        exact X.tateEval_reduction _ x⟩
    obtain ⟨f, hf⟩ := exists_seq_forall_proj_of_forall_finite π
      (by intro i a; apply Subtype.ext; change genericHom (X.reduction _) a.val = a.val
          rw [X.reduction_refl, genericHom_id])
      (by intro i j k h h' a; apply Subtype.ext
          exact X.pointReduction_comp h h' a.val)
      (fun _ _ ↦ Set.toFinite _)
    refine ⟨⟨fun k ↦ (f k).val, fun h ↦ congrArg Subtype.val (hf h)⟩, ?_⟩
    apply X.tate_ext
    intro k
    exact (f k).property
  · rintro ⟨y, rfl⟩
    rw [map_nsmul]
    exact X.killed m _

/-- The actual evaluation kernel is precisely the submodule of p-power multiples. -/
theorem tateEvalLinear_ker (m : ℕ) :
    LinearMap.ker (X.tateEvalLinear m) =
      LinearMap.range (p ^ m • (LinearMap.id : X.tateSequences →ₗ[ℤ_[p]] _)) := by
  ext x
  exact X.tateEvalLinear_eq_zero_iff m x

/-- The original limit modulo p^m is the original finite point group. -/
def tateReductionEquiv (m : ℕ) :
    (X.tateSequences ⧸
      LinearMap.range (p ^ m • (LinearMap.id : X.tateSequences →ₗ[ℤ_[p]] _))) ≃ₗ[ℤ_[p]]
      (X.level m).Points :=
  (Submodule.quotEquivOfEq _ _ (X.tateEvalLinear_ker m).symm).trans
    ((X.tateEvalLinear m).quotKerEquivOfSurjective (X.tateEval_surjective_unconditional m))

/-- The reduction equivalence is induced by the specified original evaluation. -/
theorem tateReductionEquiv_mk (m : ℕ) (x : X.tateSequences) :
    X.tateReductionEquiv m (Submodule.Quotient.mk x) = X.tateEvalLinear m x := rfl

end ThreeAdicPlan.PDivisibleSystem
