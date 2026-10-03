/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.RankTwoCharpoly
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Algebra.ZMod

/-!
# The original rank-two operator on additive scalar quotients

Cayley–Hamilton is applied over the original coefficient field. Its trace-zero
identity descends through an additive quotient when the determinant is in the
prime field; the quotient's prime-field dimension is unrestricted.
-/

@[expose] public noncomputable section
namespace LinearMap
open Polynomial

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
  [Module.Finite k V] (T : Module.End k V)

/-- The original k-linear rank-two trace-zero operator squares to minus its determinant. -/
theorem square_apply_of_trace_eq_zero (hV : Module.finrank k V = 2)
    (ht : trace k V T = 0) (x : V) : T (T x) = -(T.det • x) := by
  have h := T.aeval_self_charpoly
  rw [T.charpoly_eq_quadratic hV, ht] at h
  have hx := congrArg (fun f : Module.End k V ↦ f x) h
  apply eq_neg_of_add_eq_zero_left
  simpa [pow_two] using hx

/-- A scalar on an actual additive quotient obeys the original quadratic identity. -/
theorem scalar_quotient_square_of_trace_eq_zero {p : ℕ} [CharP k p]
    {F W : Type*} [Field F] [CharP F p] [AddCommGroup W] [Module F W] [Nontrivial W]
    (hV : Module.finrank k V = 2) (ht : trace k V T = 0)
    (c : ZMod p) (hdet : T.det = ZMod.castHom (dvd_refl p) k c)
    (q : V →+ W) (hq : Function.Surjective q) (a : F)
    (ha : ∀ x, q (T x) = a • q x) :
    a ^ 2 = -(ZMod.castHom (dvd_refl p) F c) := by
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨x, rfl⟩ := hq w
  have h := congrArg q (T.square_apply_of_trace_eq_zero hV ht x)
  rw [ha, ha, smul_smul, ← pow_two, hdet, map_neg] at h
  have hc : q ((ZMod.castHom (dvd_refl p) k c) • x) =
      (ZMod.castHom (dvd_refl p) F c) • q x := by
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective c
    simp only [map_intCast, Int.cast_smul_eq_zsmul, map_zsmul]
  rw [hc, ← neg_smul] at h
  exact (smul_left_injective F hw) h

end LinearMap
