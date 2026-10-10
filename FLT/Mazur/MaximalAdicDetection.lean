/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Ideal.Maximal

/-!
# Detection by all maximal-ideal-adic quotients

An element of a finite module over a Noetherian ring is zero if it belongs
to every power of every maximal ideal times the module. Krull intersection
produces an annihilator outside any maximal ideal containing its annihilator.
-/

@[expose] public section
namespace FLT.Mazur.MaximalAdicDetection

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [IsNoetherianRing R] [Module.Finite R M]

/-- All maximal-ideal powers together separate a finite module over a Noetherian ring. -/
theorem eq_zero (x : M)
    (hx : ∀ (J : Ideal R), J.IsMaximal → ∀ n : ℕ,
      x ∈ J ^ n • (⊤ : Submodule R M)) : x = 0 := by
  let K : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R M x)
  by_contra hne
  have hK : K ≠ ⊤ := by
    intro h
    have h1 : (1 : R) ∈ K := h.symm ▸ Submodule.mem_top
    change (1 : R) • x = 0 at h1
    exact hne (by simpa using h1)
  obtain ⟨J, hJ, hKJ⟩ := Ideal.exists_le_maximal K hK
  obtain ⟨r, hr⟩ := (J.mem_iInf_smul_pow_eq_bot_iff x).mp
    (by rw [Submodule.mem_iInf]; exact hx J hJ)
  have hsub : 1 - (r : R) ∈ K := by
    change (1 - (r : R)) • x = 0
    rw [sub_smul, one_smul, hr, sub_self]
  have h1 : (1 : R) ∈ J := by
    have h := J.add_mem (hKJ hsub) r.property
    simpa only [sub_add_cancel] using h
  exact hJ.ne_top (Ideal.eq_top_of_isUnit_mem J h1 isUnit_one)

end FLT.Mazur.MaximalAdicDetection
