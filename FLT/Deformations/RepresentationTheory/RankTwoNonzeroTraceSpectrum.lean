/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.MappedRankTwoCharpoly
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# The mapped rank-two spectrum with nonzero trace

Factor the actual coefficient-field characteristic polynomial. Invertibility
and nonzero trace give nonzero eigenvalues whose ratio is not minus one.
-/

@[expose] public noncomputable section
namespace LinearMap
open Polynomial

variable {k E V : Type*} [Field k] [Field E] [IsAlgClosed E]
  [AddCommGroup V] [Module k V] [Module.Finite k V]
  (T : Module.End k V) (f : k →+* E)

/-- A rank-two invertible operator with nonzero trace has the required quadratic spectrum. -/
theorem exists_map_charpoly_units_of_trace_ne_zero (hV : Module.finrank k V = 2)
    (hd : T.det ≠ 0) (ht : trace k V T ≠ 0) :
    ∃ a b : Eˣ, T.charpoly.map f = (X - C (a : E)) * (X - C (b : E)) ∧
      (a : E) + (b : E) = f (trace k V T) ∧
      (a : E) * (b : E) = f T.det ∧ a / b ≠ -1 := by
  have hdeg : (T.charpoly.map f).degree ≠ 0 := by
    rw [degree_map_eq_of_injective f.injective, degree_eq_natDegree T.charpoly_monic.ne_zero,
      T.charpoly_natDegree, hV]
    norm_num
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root (T.charpoly.map f) hdeg
  have he : a ^ 2 - f (trace k V T) * a + f T.det = 0 := by
    simpa only [T.charpoly_eq_quadratic hV, Polynomial.map_add, Polynomial.map_sub,
      Polynomial.map_mul, Polynomial.map_pow, map_X, map_C, IsRoot, eval_add, eval_sub,
      eval_mul, eval_pow, eval_X, eval_C] using ha
  let b := f (trace k V T) - a
  have hab : a * b = f T.det := by dsimp [b]; linear_combination -he
  have hab0 : a * b ≠ 0 := hab ▸ ((_root_.map_ne_zero f).mpr hd)
  let au : Eˣ := Units.mk0 a (left_ne_zero_of_mul hab0)
  let bu : Eˣ := Units.mk0 b (right_ne_zero_of_mul hab0)
  refine ⟨au, bu, ?_, ?_, hab, ?_⟩
  · rw [T.charpoly_eq_quadratic hV]
    simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
      Polynomial.map_pow, map_X, map_C]
    change X ^ 2 - C (f (trace k V T)) * X + C (f T.det) = (X - C a) * (X - C b)
    rw [← hab]
    have hs : f (trace k V T) = a + b := by dsimp [b]; ring
    rw [hs, map_add, map_mul]
    ring
  · change a + b = f (trace k V T)
    dsimp [b]
    ring
  · intro h
    have hu : au = -bu := (div_eq_iff_eq_mul).mp h |>.trans (neg_one_mul bu)
    have hv : a = -b := congrArg Units.val hu
    apply (_root_.map_ne_zero f).mpr ht
    dsimp [b] at hv
    linear_combination hv

end LinearMap
