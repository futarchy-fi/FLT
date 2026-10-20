/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicDiscrepancySeparation
public import FLT.Mazur.SubmoduleQuotientScalarReduction

/-!
# Original corrections from arbitrarily accurate adic corrections

Approximation uses the unchanged ambient module and its actual correction
submodule. Finiteness is required only for the correction quotient, over the
original scalar ring. No flatness of reduction or completeness is used.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.AdicCorrectionClosure
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (I : Ideal R) (K : Submodule R M)

/-- An approximate original correction is precisely an adically small quotient class. -/
theorem quotient_mem_iff (n : ℕ) (x : M) :
    K.mkQ x ∈ I ^ n • (⊤ : Submodule R (M ⧸ K)) ↔
      x ∈ K ⊔ I ^ n • (⊤ : Submodule R M) := by
  change x ∈ (I ^ n • (⊤ : Submodule R (M ⧸ K))).comap K.mkQ ↔ _
  rw [RelativeSubmoduleQuotient.comap_quotient_smul_top]

variable [IsNoetherianRing R] [Module.Finite R (M ⧸ K)]

/-- All positive-order approximations give an exact correction after one original scalar. -/
theorem exists_scalar_correction (x : M)
    (hx : ∀ n : ℕ, x ∈ K ⊔ I ^ (n + 1) • (⊤ : Submodule R M)) :
    ∃ s : R, 1 - s ∈ I ∧ s • x ∈ K := by
  obtain ⟨s, hs, he⟩ := AdicDiscrepancySeparation.exists_annihilator I (K.mkQ x)
    (fun n ↦ (quotient_mem_iff I K (n + 1) x).mpr (hx n))
  refine ⟨s, hs, (Submodule.Quotient.mk_eq_zero K).mp ?_⟩
  exact (map_smul K.mkQ s x).trans he

/-- The exact correction scalar avoids any original prime containing the adic ideal. -/
theorem exists_scalar_correction_outside (P : Ideal R) (hIP : I ≤ P) (hP : P ≠ ⊤)
    (x : M) (hx : ∀ n : ℕ, x ∈ K ⊔ I ^ (n + 1) • (⊤ : Submodule R M)) :
    ∃ s : R, s ∉ P ∧ 1 - s ∈ I ∧ s • x ∈ K := by
  obtain ⟨s, hs, he⟩ := exists_scalar_correction I K x hx
  refine ⟨s, ?_, hs, he⟩
  intro hp
  exact hP (P.eq_top_iff_one.mpr (by simpa using P.add_mem (hIP hs) hp))

/-- Over local original scalars, all-order approximations are actual corrections. -/
theorem mem_of_local_approximations [IsLocalRing R] (hI : I ≠ ⊤) (x : M)
    (hx : ∀ n : ℕ, x ∈ K ⊔ I ^ (n + 1) • (⊤ : Submodule R M)) : x ∈ K := by
  apply (Submodule.Quotient.mk_eq_zero K).mp
  exact AdicDiscrepancySeparation.eq_zero_of_local I hI (K.mkQ x)
    (fun n ↦ (quotient_mem_iff I K (n + 1) x).mpr (hx n))

end FLT.Mazur.AdicCorrectionClosure
