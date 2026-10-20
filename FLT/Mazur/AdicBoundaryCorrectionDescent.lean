/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicCorrectionClosure
public import FLT.Mazur.RelativeBoundaryConnectingMap

/-!
# Exact boundary lifts from original adic approximations

All approximating families live on the same original source and have the
same exact boundary. Finite generation of the mixed correction quotient
turns arbitrarily small discrepancies into a single exact compatible family.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.AdicBoundaryCorrectionDescent
variable {R A B C : Type*} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]
  (b : A →ₗ[R] B) (δ : A →ₗ[R] C) (I : Ideal R)
set_option quotPrecheck false
local notation "K" => (LinearMap.ker b).map δ

/-- Two exact lifts of one boundary differ by an actual boundary-zero correction. -/
theorem discrepancy_mem_of_approximation (u v : A) (hb : b v = b u) (n : ℕ)
    (hv : δ v ∈ I ^ n • (⊤ : Submodule R C)) :
    δ u ∈ K ⊔ I ^ n • (⊤ : Submodule R C) := by
  apply Submodule.mem_sup.mpr
  refine ⟨δ (u - v), ⟨u - v, ?_, rfl⟩, δ v, hv, ?_⟩
  · change b (u - v) = 0
    rw [map_sub, hb, sub_self]
  · rw [map_sub, sub_add_cancel]

/-- An exact correction to a scaled discrepancy preserves the scaled original boundary. -/
theorem exists_lift_of_scalar_correction (u : A) (s : R) (hs : s • δ u ∈ K) :
    ∃ v : A, b v = s • b u ∧ δ v = 0 := by
  obtain ⟨z, hz, he⟩ := hs
  refine ⟨s • u - z, ?_, ?_⟩
  · rw [map_sub, map_smul, LinearMap.mem_ker.mp hz, sub_zero]
  · rw [map_sub, map_smul, he, sub_self]

variable [IsNoetherianRing R]
  [Module.Finite R (C ⧸ (LinearMap.ker b).map δ)]

/-- Arbitrarily accurate original families produce one exact original compatible numerator. -/
theorem exists_scaled_lift (P : Ideal R) (hIP : I ≤ P) (hP : P ≠ ⊤) (u : A)
    (h : ∀ n : ℕ, ∃ v : A, b v = b u ∧
      δ v ∈ I ^ (n + 1) • (⊤ : Submodule R C)) :
    ∃ s : R, s ∉ P ∧ 1 - s ∈ I ∧ ∃ v : A, b v = s • b u ∧ δ v = 0 := by
  obtain ⟨s, hs, hi, he⟩ := AdicCorrectionClosure.exists_scalar_correction_outside I K
    P hIP hP (δ u) (fun n ↦ by
      obtain ⟨v, hb, hv⟩ := h n
      exact discrepancy_mem_of_approximation b δ I u v hb (n + 1) hv)
  exact ⟨s, hs, hi, exists_lift_of_scalar_correction b δ u s he⟩

/-- With local original scalars, approximation gives a lift with the unchanged boundary. -/
theorem exists_lift_of_local [IsLocalRing R] (hI : I ≠ ⊤) (u : A)
    (h : ∀ n : ℕ, ∃ v : A, b v = b u ∧
      δ v ∈ I ^ (n + 1) • (⊤ : Submodule R C)) :
    ∃ v : A, b v = b u ∧ δ v = 0 := by
  have he : δ u ∈ K := AdicCorrectionClosure.mem_of_local_approximations I K hI
    (δ u) (fun n ↦ by
      obtain ⟨v, hb, hv⟩ := h n
      exact discrepancy_mem_of_approximation b δ I u v hb (n + 1) hv)
  simpa only [one_smul] using exists_lift_of_scalar_correction b δ u 1 (by simpa using he)

end FLT.Mazur.AdicBoundaryCorrectionDescent
