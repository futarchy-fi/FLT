/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.StableCompatibleRingTower
public import FLT.Mazur.CompatibleNumeratorObstruction

/-!
# All-order numerator control from a stable geometric tail

Stable source and target transitions make one stage test sufficient. The
homogeneous ideals must also be transported exactly in the stable tail;
ordinary preservation suffices for the earlier orders.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.CompatibleRingTower
variable {R S : ℕ → Type*} [∀ k, CommRing (R k)] [∀ k, CommRing (S k)]
  (ρ : ∀ k l, k ≤ l → R l →+* R k)
  (σ : ∀ k l, k ≤ l → S l →+* S k) (f : ∀ k, R k →+* S k)
  (hsq : ∀ k l (h : k ≤ l) z, f k (ρ k l h z) = σ k l h (f l z))
  (hcomp : ∀ k l m (h : k ≤ l) (h' : l ≤ m) z,
    ρ k l h (ρ l m h' z) = ρ k m (h.trans h') z)
  (K : ℕ) (hρ : ∀ l (h : K ≤ l), Function.Bijective (ρ K l h))
  (hσ : ∀ l (h : K ≤ l), Function.Bijective (σ K l h))
  (I : ∀ k, Ideal (R k))
  (hI : ∀ k l (h : k ≤ l) z, z ∈ I l → ρ k l h z ∈ I k)
  (hIK : ∀ l (h : K ≤ l) z, ρ K l h z ∈ I K → z ∈ I l)

include hI hIK in
/-- One full boundary equation detects all boundary equations in a stable tower. -/
theorem stable_mem_ideal_iff (w : ring ρ) : w ∈ ideal ρ I ↔ w.val K ∈ I K := by
  constructor
  · exact fun hw ↦ hw K
  · intro hw k
    by_cases hk : K ≤ k
    · exact hIK k hk _ ((w.property K k hk).symm ▸ hw)
    · have hk' : k ≤ K := Nat.le_of_not_ge hk
      rw [← w.property k K hk']
      exact hI k K hk' _ hw

include hcomp hρ hσ hI hIK in
/-- A single stable numerator extends to an ordinary compatible homogeneous numerator. -/
theorem stable_mem_numeratorIdeal_iff (x : ring σ) (a : ring ρ) :
    a ∈ numeratorIdeal ρ σ f hsq I x ↔
      a.val K ∈ HomogeneousNumeratorObstruction.scalarIdeal (f K) (I K) (x.val K) := by
  constructor
  · exact fun ha ↦ numeratorIdeal_le_stage ρ σ f hsq I x K ha
  · rintro ⟨z, hz, he⟩
    obtain ⟨w, hw⟩ := stable_eval_surjective ρ hcomp K hρ z
    have hw' : w.val K = z := hw
    refine ⟨w, (stable_mem_ideal_iff ρ K I hI hIK w).mpr (hw'.symm ▸ hz), ?_⟩
    apply stable_eval_injective σ K hσ
    change f K (w.val K) = f K (a.val K) * x.val K
    rw [hw', he]

include hcomp hρ hσ hI hIK in
/-- Stable geometry permits an actual all-order power bound from one stage power bound. -/
theorem stable_mem_radical_numeratorIdeal_iff (x : ring σ) (a : ring ρ) :
    a ∈ (numeratorIdeal ρ σ f hsq I x).radical ↔
      a.val K ∈ (HomogeneousNumeratorObstruction.scalarIdeal (f K) (I K)
        (x.val K)).radical := by
  simp only [Ideal.mem_radical_iff,
    stable_mem_numeratorIdeal_iff ρ σ f hsq hcomp K hρ hσ I hI hIK,
    Subring.coe_pow, Pi.pow_apply]

end FLT.Mazur.CompatibleRingTower
