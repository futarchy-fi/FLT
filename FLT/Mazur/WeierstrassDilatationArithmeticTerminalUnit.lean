/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationArithmeticTerminalNode

/-!
# Unit comparison for the actual terminal smoothing

If the original b6 has a unit first-order coefficient, the constructed terminal
smoothing is a unit multiple of the arithmetic parameter. The correction follows
from the already proved second-order congruence, not from an assumed node comparison.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
open PolygonArithmeticStages

/-- A nilpotent second-order correction preserves a unit linear coefficient. -/
theorem exists_unit_mul_of_sub_mem_square {A : Type*} [CommRing A]
    (t c : A) (ht : IsNilpotent t) (u : Aˣ)
    (hc : c - t * ↑u ∈ (Ideal.span ({t} : Set A)) ^ 2) :
    ∃ v : Aˣ, c = t * ↑v := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hc
  obtain ⟨z, hz⟩ := hc
  have hu : IsUnit ((u : A) + t * z) :=
    ((Commute.all t z).isNilpotent_mul_right ht).isUnit_add_left_of_commute
      u.isUnit (Commute.all _ _)
  refine ⟨hu.unit, ?_⟩
  rw [hu.unit_spec]
  calc
    c = t * ↑u + (c - t * ↑u) := by ring
    _ = t * (↑u + t * z) := by rw [hz]; ring

variable {R : Type*} [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (hs : π ∣ s) (h2 : π ∣ W.a₂)
  (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)
local notation "Q" => Quotient R π m
local notation "c" => arithmeticTerminalSmoothing π m W s b3 b4 b6 ha hs h2 h4 h6

include h3 in
/-- A primitive original b6 gives the needed unit scaling at every quotient order. -/
theorem arithmeticTerminalSmoothing_exists_unit (u : Rˣ) (hu : b6 = π * ↑u) :
    ∃ v : Qˣ, c = parameter R π m * ↑v := by
  apply exists_unit_mul_of_sub_mem_square (parameter R π m) c
    ⟨m + 1, parameter_pow R π m⟩ (Units.map (algebraMap R Q) u)
  have hc := arithmeticTerminalSmoothing_sub_mem_sq π m W s b3 b4 b6
    ha hs h2 h4 h6 h3
  simpa only [hu, map_mul, Units.coe_map, MonoidHom.coe_ofClass, parameter, ideal] using hc

end FLT.Mazur.WeierstrassDilatation
