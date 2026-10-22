/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteIdealResidualPowers
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# One scalar correction from finitely many full coefficient equations

Each chart may choose its own residual scalar. A finite product replaces
these choices by one scalar that works on every chart, after an explicit
power. Coefficient rings retain all nilpotents; no scalar extension is used.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteScalarResidualCorrections
open scoped BigOperators
variable {R : Type*} [CommRing R] {ι : Type*}
  {B : ι → Type*} [∀ i, CommRing (B i)] (f : ∀ i, R →+* B i) (J : Ideal R)

/-- A sum with an exact kernel means equality with an original residual scalar. -/
theorem mem_kernel_sup_iff {C : Type*} [CommRing C] (g : R →+* C) (a : R) :
    a ∈ RingHom.ker g ⊔ J ↔ ∃ b ∈ J, g a = g b := by
  constructor
  · intro ha
    obtain ⟨u, hu, b, hb, rfl⟩ := Submodule.mem_sup.mp ha
    exact ⟨b, hb, by rw [map_add, RingHom.mem_ker.mp hu, zero_add]⟩
  · rintro ⟨b, hb, hab⟩
    exact Submodule.mem_sup.mpr
      ⟨a - b, RingHom.mem_ker.mpr (by rw [map_sub, hab, sub_self]), b, hb,
        sub_add_cancel a b⟩

/-- An intersection before adding the residual ideal requires a single shared correction. -/
theorem mem_iInf_kernel_sup_iff (a : R) :
    a ∈ (⨅ i, RingHom.ker (f i)) ⊔ J ↔ ∃ b ∈ J, ∀ i, f i a = f i b := by
  constructor
  · intro ha
    obtain ⟨u, hu, b, hb, rfl⟩ := Submodule.mem_sup.mp ha
    refine ⟨b, hb, fun i ↦ ?_⟩
    rw [map_add, RingHom.mem_ker.mp ((Ideal.mem_iInf.mp hu) i), zero_add]
  · rintro ⟨b, hb, hab⟩
    refine Submodule.mem_sup.mpr ⟨a - b, ?_, b, hb, sub_add_cancel a b⟩
    exact Ideal.mem_iInf.mpr fun i ↦
      RingHom.mem_ker.mpr (by rw [map_sub, hab i, sub_self])

variable [Finite ι]

/-- Chartwise exact powers combine with the explicit number of coefficient tests. -/
theorem pow_le_shared_kernel (Q : Ideal R) (k : ℕ)
    (h : ∀ i, Q ^ k ≤ RingHom.ker (f i) ⊔ J) :
    Q ^ (Nat.card ι * k) ≤ (⨅ i, RingHom.ker (f i)) ⊔ J := by
  classical
  let _ := Fintype.ofFinite ι
  simpa only [Finset.card_univ, Fintype.card_eq_nat_card, Finset.inf_univ_eq_iInf] using
    FiniteIdealResidualPowers.pow_card_mul_le_inf_sup Finset.univ
      (fun i ↦ RingHom.ker (f i)) J Q k (fun i _ ↦ h i)

/-- Independent scalar corrections produce one full coefficient correction after a power. -/
theorem exists_shared_correction (Q : Ideal R) (k : ℕ)
    (h : ∀ i a, a ∈ Q ^ k → ∃ b ∈ J, f i a = f i b)
    (a : R) (ha : a ∈ Q ^ (Nat.card ι * k)) :
    ∃ b ∈ J, ∀ i, f i a = f i b := by
  apply (mem_iInf_kernel_sup_iff f J a).mp
  exact pow_le_shared_kernel f J Q k
    (fun i a ha ↦ (mem_kernel_sup_iff J (f i) a).mpr (h i a ha)) ha

/-- Finite generation is needed only when converting chartwise radical equations to powers. -/
theorem exists_pow_le_shared_kernel (Q : Ideal R) (hfg : Q.FG)
    (h : ∀ i, Q ≤ (RingHom.ker (f i) ⊔ J).radical) :
    ∃ k : ℕ, Q ^ k ≤ (⨅ i, RingHom.ker (f i)) ⊔ J := by
  classical
  let _ := Fintype.ofFinite ι
  choose k hk using fun i ↦ Ideal.exists_pow_le_of_le_radical_of_fg (h i) hfg
  refine ⟨∑ i, k i, ?_⟩
  simpa only [Finset.inf_univ_eq_iInf] using
    FiniteIdealResidualPowers.pow_sum_le_inf_sup Finset.univ
      (fun i ↦ RingHom.ker (f i)) J Q k (fun i _ ↦ hk i)

end FLT.Mazur.FiniteScalarResidualCorrections
