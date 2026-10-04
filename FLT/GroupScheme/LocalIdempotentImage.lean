/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.LocalRing.Quotient

/-! # Images of pointed local component idempotents under closed immersions -/

@[expose] public noncomputable section
namespace ThreeAdicPlan
variable {A B R : Type*} [CommRing A] [CommRing B] [CommRing R] [Nontrivial R]

/-- Equality to one in an idempotent factor detects multiplication by that idempotent. -/
theorem mul_eq_self_of_component_eq_one {e x : B} (he : IsIdempotentElem e)
    (hx : Ideal.Quotient.mk (Ideal.span {1 - e}) x = 1) : e * x = e := by
  have hm : x - 1 ∈ Ideal.span {1 - e} := Ideal.Quotient.eq_zero_iff_mem.mp (by
    rw [map_sub, map_one, hx, sub_self])
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hm
  have h := congrArg (e * ·) ha
  rw [← mul_assoc, he.mul_one_sub_self, zero_mul, mul_sub, mul_one] at h
  exact sub_eq_zero.mp h

/-- A surjective ring map takes a component with local coordinates to the unique
pointed local component on its image. The point makes both factors nonempty. -/
theorem map_local_component_idempotent (f : A →+* B) (hf : Function.Surjective f)
    (ε : B →+* R) {e : A} {d : B} (he : IsIdempotentElem e)
    (hd : IsIdempotentElem d) [IsLocalRing (A ⧸ Ideal.span {1 - e})]
    (heε : ε (f e) = 1) (hdε : ε d = 1)
    (hed : Ideal.Quotient.mk (Ideal.span {1 - d}) (f e) = 1) : f e = d := by
  let J : Ideal B := Ideal.span {1 - f e}
  have hJε : J ≤ RingHom.ker ε := by
    apply Ideal.span_le.mpr
    rintro x (rfl : x = _)
    change ε (1 - f e) = 0
    rw [map_sub, map_one, heε, sub_self]
  let ε' : B ⧸ J →+* R := Ideal.Quotient.lift J ε hJε
  let : Nontrivial (B ⧸ J) := ε'.domain_nontrivial
  have hIJ : Ideal.span {1 - e} ≤ J.comap f := by
    apply Ideal.span_le.mpr
    rintro x (rfl : x = _)
    change f (1 - e) ∈ J
    rw [map_sub, map_one]
    exact Ideal.mem_span_singleton_self _
  let q : (A ⧸ Ideal.span {1 - e}) →+* B ⧸ J := Ideal.quotientMap J f hIJ
  have hq : Function.Surjective q := Ideal.quotientMap_surjective hf
  let : IsLocalRing (B ⧸ J) := IsLocalRing.of_surjective' q hq
  have hdJ : Ideal.Quotient.mk J d = 1 := by
    apply IsIdempotentElem.iff_eq_one_of_isUnit ?_ |>.mp (hd.map (Ideal.Quotient.mk J))
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (Ideal.Quotient.mk J d) with h | h
    · exact h
    · have hz := h.map ε'
      have heval : ε' (1 - Ideal.Quotient.mk J d) = 0 := by
        rw [map_sub, map_one]
        change 1 - ε d = 0
        rw [hdε, sub_self]
      rw [heval] at hz
      exact (not_isUnit_zero hz).elim
  have h₁ := mul_eq_self_of_component_eq_one (he.map f) hdJ
  have h₂ := mul_eq_self_of_component_eq_one hd hed
  exact h₁.symm.trans ((mul_comm _ _).trans h₂)
end ThreeAdicPlan
