/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicLinearImageDescent

/-!
# Lifting actual reduced linear equations to original approximations

The reduction is the quotient by powers of the original scalar ideal on
both modules. Representatives of reduced solutions supply full original
approximations without flatness, compatible choices, or tensor expansion.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.AdicLinearImageDescent
variable {R A M : Type*} [CommRing R] [AddCommGroup A] [Module R A]
  [AddCommGroup M] [Module R M] (F : A →ₗ[R] M) (I : Ideal R)

/-- The actual original equation map reduced by a scalar ideal power. -/
def reduction (n : ℕ) :
    (A ⧸ I ^ n • (⊤ : Submodule R A)) →ₗ[R] M ⧸ I ^ n • (⊤ : Submodule R M) :=
  (I ^ n • (⊤ : Submodule R A)).mapQ (I ^ n • (⊤ : Submodule R M)) F
    (Submodule.smul_top_le_comap_smul_top (I ^ n) F)

/-- Reduction retains the original equation vector of every representative. -/
theorem reduction_mk (n : ℕ) (v : A) :
    reduction F I n ((I ^ n • (⊤ : Submodule R A)).mkQ v) =
      (I ^ n • (⊤ : Submodule R M)).mkQ (F v) := rfl

/-- A reduced solution is exactly an original solution up to that full ideal power. -/
theorem exists_reduced_solution_iff (n : ℕ) (x : M) :
    (∃ v, reduction F I n v = (I ^ n • (⊤ : Submodule R M)).mkQ x) ↔
      ∃ v : A, x - F v ∈ I ^ n • (⊤ : Submodule R M) := by
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨w, rfl⟩ := (I ^ n • (⊤ : Submodule R A)).mkQ_surjective v
    refine ⟨w, (Submodule.Quotient.mk_eq_zero _).mp ?_⟩
    change (I ^ n • (⊤ : Submodule R M)).mkQ (x - F w) = 0
    rw [map_sub, ← reduction_mk, hv, sub_self]
  · rintro ⟨v, hv⟩
    refine ⟨(I ^ n • (⊤ : Submodule R A)).mkQ v, ?_⟩
    rw [reduction_mk]
    apply eq_comm.mp
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact (Submodule.Quotient.mk_eq_zero _).mpr hv

variable [IsNoetherianRing R] [Module.Finite R (M ⧸ LinearMap.range F)]

/-- Every positive original reduction solving the target gives one exact scalar numerator. -/
theorem exists_scaled_solution_of_reductions (P : Ideal R) (hIP : I ≤ P)
    (hP : P ≠ ⊤) (x : M)
    (h : ∀ n : ℕ, ∃ v, reduction F I (n + 1) v =
      (I ^ (n + 1) • (⊤ : Submodule R M)).mkQ x) :
    ∃ s : R, s ∉ P ∧ 1 - s ∈ I ∧ ∃ v : A, F v = s • x :=
  exists_scaled_solution F I P hIP hP x
    (fun n ↦ (exists_reduced_solution_iff F I (n + 1) x).mp (h n))

/-- Actual local equations descend from all their original reductions. -/
theorem exists_solution_of_local_reductions [IsLocalRing R] (hI : I ≠ ⊤) (x : M)
    (h : ∀ n : ℕ, ∃ v, reduction F I (n + 1) v =
      (I ^ (n + 1) • (⊤ : Submodule R M)).mkQ x) : ∃ v : A, F v = x :=
  exists_solution_of_local F I hI x
    (fun n ↦ (exists_reduced_solution_iff F I (n + 1) x).mp (h n))

end FLT.Mazur.AdicLinearImageDescent
