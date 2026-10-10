/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HomogeneousIdealWitness
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Order.WellFoundedSet

/-!
# Homogeneous prime avoidance

Stacks 00JS: an irrelevant homogeneous ideal not contained in any of finitely
many homogeneous primes contains a positive homogeneous element avoiding them all.
The induction removes a minimal prime, so it does not need an antichain hypothesis.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace FLT.Mazur.HomogeneousAvoidance

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Positive homogeneous prime avoidance, with no restriction on residue fields. -/
theorem exists_positive_avoiding (I : HomogeneousIdeal 𝒜)
    (hI : I ≤ HomogeneousIdeal.irrelevant 𝒜) (s : Finset (HomogeneousIdeal 𝒜))
    (hp : ∀ P ∈ s, P.toIdeal.IsPrime) (hnot : ∀ P ∈ s, ¬ I ≤ P) :
    ∃ (n : ℕ) (x : A), 0 < n ∧ x ∈ 𝒜 n ∧ x ∈ I ∧ ∀ P ∈ s, x ∉ P := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hs : s.Nonempty
    · obtain ⟨P, hPs, hmin⟩ := s.finite_toSet.isPWO.exists_minimal hs
      let t := s.erase P
      have ht : t ⊂ s := Finset.erase_ssubset hPs
      obtain ⟨d, x, hd, hxd, hxI, hxt⟩ :=
        ih t ht (fun Q hQ ↦ hp Q (ht.1 hQ)) (fun Q hQ ↦ hnot Q (ht.1 hQ))
      by_cases hxP : x ∈ P
      · let J : HomogeneousIdeal 𝒜 := I ⊓ ⨅ Q ∈ t, Q
        have hJ : ¬ J ≤ P := by
          change ¬ J.toIdeal ≤ P.toIdeal
          dsimp only [J]
          rw [HomogeneousIdeal.toIdeal_inf, (hp P hPs).inf_le]
          simp_rw [HomogeneousIdeal.toIdeal_iInf]
          rw [← Finset.inf_eq_iInf]
          rw [(hp P hPs).inf_le']
          rintro (h | ⟨Q, hQt, hQP⟩)
          · exact hnot P hPs h
          · exact (Finset.mem_erase.mp hQt).1
              (le_antisymm hQP (hmin (ht.1 hQt) hQP))
        obtain ⟨e, y, he, hye, hyJ, hyP⟩ :=
          exists_positive_not_mem 𝒜 J P (inf_le_left.trans hI) hJ
        have hyI : y ∈ I := hyJ.1
        have hyt (Q) (hQt : Q ∈ t) : y ∈ Q := by
          exact (show (⨅ Q ∈ t, Q : HomogeneousIdeal 𝒜) ≤ Q from
            iInf_le_of_le Q (iInf_le_of_le hQt le_rfl)) hyJ.2
        refine ⟨e * d, x ^ e + y ^ d, Nat.mul_pos he hd, ?_, ?_, ?_⟩
        · apply add_mem
          · simpa only [nsmul_eq_mul, Nat.cast_id] using SetLike.pow_mem_graded e hxd
          · simpa only [nsmul_eq_mul, Nat.cast_id, Nat.mul_comm] using SetLike.pow_mem_graded d hye
        · exact I.toIdeal.add_mem (I.toIdeal.pow_mem_of_mem hxI e he)
            (I.toIdeal.pow_mem_of_mem hyI d hd)
        · intro Q hQs hsum
          by_cases hQP : Q = P
          · subst Q
            have hyPow := P.toIdeal.sub_mem hsum (P.toIdeal.pow_mem_of_mem hxP e he)
            have : y ^ d ∈ P := by
              simpa only [add_sub_cancel_left, HomogeneousIdeal.mem_iff] using hyPow
            exact hyP ((hp P hPs).mem_of_pow_mem d this)
          · have hQt : Q ∈ t := Finset.mem_erase.mpr ⟨hQP, hQs⟩
            have hxPow := Q.toIdeal.sub_mem hsum (Q.toIdeal.pow_mem_of_mem (hyt Q hQt) d hd)
            have : x ^ e ∈ Q := by
              simpa only [add_sub_cancel_right, HomogeneousIdeal.mem_iff] using hxPow
            exact hxt Q hQt ((hp Q hQs).mem_of_pow_mem e this)
      · refine ⟨d, x, hd, hxd, hxI, fun Q hQs ↦ ?_⟩
        by_cases hQP : Q = P
        · exact hQP ▸ hxP
        · exact hxt Q (Finset.mem_erase.mpr ⟨hQP, hQs⟩)
    · have hs' : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      exact ⟨1, 0, Nat.one_pos, zero_mem _, I.toIdeal.zero_mem, by simp⟩

end FLT.Mazur.HomogeneousAvoidance
