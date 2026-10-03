/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.RankTwoCharpoly
public import FLT.Deformations.RepresentationTheory.TameSpectrumDigits

/-!
# Binary tame weights assembled at the characteristic polynomial

The determinant selects complementary digits and hence a nonzero trace.
The factorization hypotheses remain explicit: constructing them from a
finite-flat model is a separate arithmetic theorem.
-/

@[expose] public noncomputable section
namespace Representation
open Polynomial

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
  [Module.Finite k V] (T : Module.End k V) (hV : Module.finrank k V = 2)
  {p a b : ℕ} {z : kˣ}

include hV

/-- Ordinary binary factors and cyclotomic determinant give the canonical spectrum. -/
theorem ordinary_charpoly_of_digits (hp : 3 < p) (hz : orderOf z = p - 1)
    (ha : a ≤ 1) (hb : b ≤ 1) (hd : T.det = (z : k))
    (hf : T.charpoly = (X - C ((z ^ a : kˣ) : k)) * (X - C ((z ^ b : kˣ) : k))) :
    T.charpoly = (X - C 1) * (X - C (z : k)) := by
  have hd' : z ^ a * z ^ b = z := by
    apply Units.ext
    exact ((T.trace_det_of_charpoly_factors hV _ _ hf).2.symm.trans hd)
  rcases ordinary_digits hp hz ha hb hd' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simpa using hf
  · simpa only [pow_zero, pow_one, Units.val_one, mul_comm] using hf

/-- The ordinary binary-weight spectrum has nonzero trace at a generator. -/
theorem ordinary_trace_ne_zero_of_digits (hp : 3 < p) (hz : orderOf z = p - 1)
    (ha : a ≤ 1) (hb : b ≤ 1) (hd : T.det = (z : k))
    (hf : T.charpoly = (X - C ((z ^ a : kˣ) : k)) * (X - C ((z ^ b : kˣ) : k))) :
    LinearMap.trace k V T ≠ 0 := by
  rw [(T.trace_det_of_charpoly_factors hV _ _
    (ordinary_charpoly_of_digits T hV hp hz ha hb hd hf)).1]
  exact ordinary_sum_ne_zero hp hz

/-- Frobenius-conjugate binary factors and their determinant give the niveau-two spectrum. -/
theorem niveau_two_charpoly_of_digits (hp : 3 < p) (hz : orderOf z = p * p - 1)
    (ha : a ≤ 1) (hb : b ≤ 1) (hd : T.det = ((z ^ (p + 1) : kˣ) : k))
    (hf : T.charpoly = (X - C ((z ^ (a + p * b) : kˣ) : k)) *
      (X - C ((z ^ (p * a + b) : kˣ) : k))) :
    T.charpoly = (X - C (z : k)) * (X - C ((z ^ p : kˣ) : k)) := by
  have hd' : z ^ (a + p * b) * z ^ (p * a + b) = z ^ (p + 1) := by
    apply Units.ext
    exact ((T.trace_det_of_charpoly_factors hV _ _ hf).2.symm.trans hd)
  rcases niveau_two_digits hp hz ha hb hd' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simpa [mul_comm] using hf
  · simpa using hf

/-- The niveau-two binary-weight spectrum has nonzero trace at a generator. -/
theorem niveau_two_trace_ne_zero_of_digits (hp : 3 < p) (hz : orderOf z = p * p - 1)
    (ha : a ≤ 1) (hb : b ≤ 1) (hd : T.det = ((z ^ (p + 1) : kˣ) : k))
    (hf : T.charpoly = (X - C ((z ^ (a + p * b) : kˣ) : k)) *
      (X - C ((z ^ (p * a + b) : kˣ) : k))) :
    LinearMap.trace k V T ≠ 0 := by
  rw [(T.trace_det_of_charpoly_factors hV _ _
    (niveau_two_charpoly_of_digits T hV hp hz ha hb hd hf)).1]
  exact niveau_two_sum_ne_zero (by omega) hz

end Representation
