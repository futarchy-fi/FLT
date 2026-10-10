/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Local support of a finite quotient

A quotient finite over a field stays Artinian after localizing the ambient ring.
Every prime in its support contracts to a nonzero prime in any polynomial
coordinate. No rationality assumption on the support points is needed.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FCurve

variable {K B : Type*} [Field K] [CommRing B] [Algebra K B]

/-- Localizing the ambient ring preserves Artinianness of its finite quotient. -/
theorem artinian_localized_finite_quotient (I : Ideal B) [Module.Finite K (B ⧸ I)]
    (M : Submonoid B) (L : Type*) [CommRing L] [Algebra B L] [IsLocalization M L] :
    IsArtinianRing (L ⧸ I.map (algebraMap B L)) := by
  let _ : IsArtinianRing (B ⧸ I) := IsArtinianRing.of_finite K (B ⧸ I)
  exact IsArtinianRing.localization_artinian
    (Algebra.algebraMapSubmonoid (B ⧸ I) M) _

/-- A polynomial coordinate has nonzero contraction at every finite-support prime. -/
theorem coordinate_prime_ne_bot_of_finite_quotient
    (g : Polynomial K →ₐ[K] B) (I : Ideal B) [Module.Finite K (B ⧸ I)]
    (q : Ideal B) (hIq : I ≤ q) : q.comap g.toRingHom ≠ ⊥ := by
  let x : B ⧸ I := Ideal.Quotient.mk I (g Polynomial.X)
  obtain ⟨p, hp, he⟩ := IsIntegral.of_finite K x
  change Polynomial.aeval x p = 0 at he
  have hm : g p ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change (Ideal.Quotient.mkₐ K I).comp g p = 0
    have hx : x = ((Ideal.Quotient.mkₐ K I).comp g) Polynomial.X := rfl
    rw [hx, Polynomial.aeval_algHom_apply, Polynomial.aeval_X_left_apply] at he
    exact he
  intro h
  have hz : p = 0 := by
    have : p ∈ q.comap g.toRingHom := hIq hm
    rw [h, Ideal.mem_bot] at this
    exact this
  exact hp.ne_zero hz

end FLT.Mazur.FCurve
