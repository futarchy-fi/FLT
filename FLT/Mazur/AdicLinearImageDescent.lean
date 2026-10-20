/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicCorrectionClosure
public import FLT.Mazur.OriginalScalarFiniteRelationDescent

/-!
# Descending approximate solutions of original linear equations

The entire equation vector is approximated, including boundary equations.
A finite cokernel over the original scalars yields an exact numerator; finite
generation of the target submodule supplies one denominator for all targets.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.AdicLinearImageDescent
variable {R A M : Type*} [CommRing R] [AddCommGroup A] [Module R A]
  [AddCommGroup M] [Module R M] (F : A →ₗ[R] M) (I : Ideal R)

/-- An approximate solution places the unchanged target in the image plus the adic error. -/
theorem mem_range_sup_of_approximation (x : M) (n : ℕ) (v : A)
    (hv : x - F v ∈ I ^ n • (⊤ : Submodule R M)) :
    x ∈ LinearMap.range F ⊔ I ^ n • (⊤ : Submodule R M) := by
  exact Submodule.mem_sup.mpr
    ⟨F v, ⟨v, rfl⟩, x - F v, hv, by rw [add_comm, sub_add_cancel]⟩

variable [IsNoetherianRing R] [Module.Finite R (M ⧸ LinearMap.range F)]

/-- Approximation of the full equation vector gives an exact original numerator. -/
theorem exists_scaled_solution (P : Ideal R) (hIP : I ≤ P) (hP : P ≠ ⊤) (x : M)
    (h : ∀ n : ℕ, ∃ v : A, x - F v ∈ I ^ (n + 1) • (⊤ : Submodule R M)) :
    ∃ s : R, s ∉ P ∧ 1 - s ∈ I ∧ ∃ v : A, F v = s • x := by
  apply AdicCorrectionClosure.exists_scalar_correction_outside I (LinearMap.range F)
    P hIP hP x
  intro n
  obtain ⟨v, hv⟩ := h n
  exact mem_range_sup_of_approximation F I x (n + 1) v hv

/-- Local scalars recover the full target, with no rescaling and no completeness assumption. -/
theorem exists_solution_of_local [IsLocalRing R] (hI : I ≠ ⊤) (x : M)
    (h : ∀ n : ℕ, ∃ v : A, x - F v ∈ I ^ (n + 1) • (⊤ : Submodule R M)) :
    ∃ v : A, F v = x := by
  apply AdicCorrectionClosure.mem_of_local_approximations I (LinearMap.range F) hI x
  intro n
  obtain ⟨v, hv⟩ := h n
  exact mem_range_sup_of_approximation F I x (n + 1) v hv

/-- Finitely generated original target families have one denominator for every equation. -/
theorem exists_uniform_scalar (P : Ideal R) [P.IsPrime] (hIP : I ≤ P)
    (T : Submodule R M) (hT : T.FG)
    (h : ∀ x ∈ T, ∀ n : ℕ, ∃ v : A,
      x - F v ∈ I ^ (n + 1) • (⊤ : Submodule R M)) :
    ∃ s : R, s ∉ P ∧ ∀ x ∈ T, ∃ v : A, F v = s • x := by
  let Q := LinearMap.range F
  obtain ⟨s, hs, hk⟩ := OriginalScalarFiniteRelationDescent.exists_scalar_killing_relations
    P T Q.mkQ hT (fun x hx ↦ by
      obtain ⟨r, hr, _, v, hv⟩ := exists_scaled_solution F I P hIP
        (Ideal.IsPrime.ne_top inferInstance) x (h x hx)
      refine ⟨r, hr, ?_⟩
      rw [← map_smul]
      exact (Submodule.Quotient.mk_eq_zero Q).mpr ⟨v, hv⟩)
  refine ⟨s, hs, fun x hx ↦ ?_⟩
  apply (Submodule.Quotient.mk_eq_zero Q).mp
  exact (map_smul Q.mkQ s x).trans (hk hx)

end FLT.Mazur.AdicLinearImageDescent
