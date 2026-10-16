/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationFixedTerminalUnit

/-!
# First-order terminal weights in the original primitive coefficient

The actual terminal smoothing equals the original constant coefficient at
order one. The unit chosen for its normalization can therefore be eliminated
from the necessary product-weight equation.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
open PolygonArithmeticStages WeierstrassModificationX
variable {R : Type} [CommRing R]

/-- Eliminate the terminal normalization unit from its two reciprocal tangent weights. -/
theorem terminal_weight_iff_primitive (a v w : Rˣ) (t p u : R)
    (ht : t * (a : R) ^ 2 = p) (hv : t * (v : R) = p * u) :
    (↑(w / (-v⁻¹ * a)) : R) * (↑(w / a) : R) * t = t ↔
      p * (u * (w : R) ^ 2 + 1) = 0 := by
  have hc : (↑(w / (-v⁻¹ * a)) : R) * (↑(w / a) : R) * (a : R) ^ 2 =
      -((v : R) * (w : R) ^ 2) := by
    change (w : R) * ((↑a⁻¹ : R) * -(v : R)) * ((w : R) * (↑a⁻¹ : R)) *
      (a : R) ^ 2 = _
    calc
      _ = -((v : R) * (w : R) ^ 2) * ((↑a⁻¹ : R) * (a : R)) ^ 2 := by ring
      _ = _ := by rw [Units.inv_mul, one_pow, mul_one]
  have he : ((↑(w / (-v⁻¹ * a)) : R) * (↑(w / a) : R) * t - t) * (a : R) ^ 2 =
      -(p * (u * (w : R) ^ 2 + 1)) := by
    calc
      _ = t * ((↑(w / (-v⁻¹ * a)) : R) * (↑(w / a) : R) * (a : R) ^ 2) -
          t * (a : R) ^ 2 := by ring
      _ = -(t * (v : R)) * (w : R) ^ 2 - p := by rw [hc, ht]; ring
      _ = _ := by rw [hv]; ring
  rw [← sub_eq_zero, ← (a ^ 2).mul_left_eq_zero]
  change _ * (a : R) ^ 2 = 0 ↔ _
  rw [he, neg_eq_zero]

variable (π : R) (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (hs : π ∣ s) (h2 : π ∣ W.a₂)
  (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)
local notation "Q" => Quotient R π 1
local notation "c" => arithmeticTerminalSmoothing π 1 W s b3 b4 b6 ha hs h2 h4 h6

include h3 in
/-- The first arithmetic terminal smoothing is exactly the original b6, with no remaining error. -/
theorem arithmeticFirstTerminalSmoothing_eq : c = algebraMap R Q b6 := by
  have h := arithmeticTerminalSmoothing_sub_mem_sq π 1 W s b3 b4 b6 ha hs h2 h4 h6 h3
  change c - algebraMap R Q b6 ∈ (Ideal.span {parameter R π 1}) ^ 2 at h
  rw [Ideal.span_singleton_pow, parameter_pow R π 1, Ideal.span_singleton_zero,
    Ideal.mem_bot] at h
  exact sub_eq_zero.mp h

variable (u : Rˣ) (hu : b6 = π * ↑u)
local notation "v" => arithmeticFixedTerminalUnit π W s b3 b4 b6
  ha hs h2 h3 h4 h6 u hu 1
local notation "τ" => arithmeticInitialMobiusSmoothing W ha (π ^ 1) π 1

/-- The full normalized terminal factor has the primitive coefficient as its exact weight. -/
theorem arithmeticFirstTerminalUnit_weight :
    τ * (v : Q) = parameter R π 1 * algebraMap R Q (u : R) := by
  rw [← arithmeticFixedTerminalUnit_spec]
  change c = _
  rw [arithmeticFirstTerminalSmoothing_eq π W s b3 b4 b6 ha hs h2 h3 h4 h6, hu, map_mul]
  rfl

end FLT.Mazur.WeierstrassDilatation
