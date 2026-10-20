/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicCorrectionClosure
public import FLT.Mazur.RelativeReductionKernelAbsorption

/-!
# Nonflat absorption with a uniform adic shift

Artin-Rees is applied after quotienting by the actual original corrections.
Only that ambient quotient must be finite. A single shift turns sufficiently
deep ambient errors into internal multiples of the exact boundary module.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.RelativeSubmoduleQuotient
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (J : Ideal R) (N K : Submodule R M)
  [IsNoetherianRing R] [Module.Finite R (M ⧸ K)]

/-- One Artin-Rees shift absorbs all sufficiently deep relative ambient errors. -/
theorem exists_shifted_absorption :
    ∃ c : ℕ, ∀ n : ℕ,
      N ⊓ (K ⊔ J ^ (n + c) • (⊤ : Submodule R M)) ≤ K ⊔ J ^ n • N := by
  obtain ⟨c, hc⟩ := J.exists_pow_inf_eq_pow_smul (N.map K.mkQ)
  refine ⟨c, fun n x hx ↦ ?_⟩
  have hq : K.mkQ x ∈ J ^ (n + c) • (⊤ : Submodule R (M ⧸ K)) :=
    (AdicCorrectionClosure.quotient_mem_iff J K (n + c) x).mpr hx.2
  have hn : K.mkQ x ∈ N.map K.mkQ := ⟨x, hx.1, rfl⟩
  have hi : K.mkQ x ∈ J ^ n • N.map K.mkQ := by
    have he := hc (n + c) (Nat.le_add_left c n)
    rw [Nat.add_sub_cancel] at he
    have hle : J ^ n • (J ^ c • ⊤ ⊓ N.map K.mkQ) ≤ J ^ n • N.map K.mkQ :=
      smul_mono_right (J ^ n) inf_le_right
    apply hle
    rw [← he]
    exact ⟨hq, hn⟩
  rw [← Submodule.map_smul''] at hi
  obtain ⟨y, hy, he⟩ := hi
  have hk : x - y ∈ K := by
    apply (Submodule.Quotient.mk_eq_zero K).mp
    change K.mkQ (x - y) = 0
    rw [map_sub, he, sub_self]
  exact Submodule.mem_sup.mpr ⟨x - y, hk, y, hy, sub_add_cancel x y⟩

/-- All-order ambient approximation gives every prescribed internal accuracy. -/
theorem mem_internal_of_approximations (x : M) (hx : x ∈ N)
    (h : ∀ n : ℕ, x ∈ K ⊔ J ^ (n + 1) • (⊤ : Submodule R M)) (n : ℕ) :
    x ∈ K ⊔ J ^ n • N := by
  obtain ⟨c, hc⟩ := exists_shifted_absorption J N K
  apply hc n
  refine ⟨hx, ?_⟩
  have hle : K ⊔ J ^ (n + c + 1) • (⊤ : Submodule R M) ≤
      K ⊔ J ^ (n + c) • (⊤ : Submodule R M) := by
    exact sup_le_sup_left (Submodule.smul_mono
      (Ideal.pow_le_pow_right (Nat.le_succ (n + c))) le_rfl) K
  exact hle (h (n + c))

/-- Nonflat reduction is injective when every lost class admits original adic corrections. -/
theorem reducedInclusion_injective_of_approximations (hKN : K ≤ N)
    (h : ∀ x ∈ N ⊓ J • (⊤ : Submodule R M), ∀ n : ℕ,
      x ∈ K ⊔ J ^ (n + 1) • (⊤ : Submodule R M)) :
    Function.Injective (reducedInclusion J N K) := by
  apply (reducedInclusion_injective_iff_absorption J N K hKN).mpr
  intro x hx
  simpa only [pow_one] using mem_internal_of_approximations J N K x hx.1 (h x hx) 1

end FLT.Mazur.RelativeSubmoduleQuotient
