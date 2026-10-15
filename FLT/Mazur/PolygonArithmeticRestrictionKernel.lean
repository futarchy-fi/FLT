/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticStageCoefficients

/-!
# The exact adjacent arithmetic coefficient kernel

Adjacent restriction is surjective with kernel the last power of the original
parameter. Its kernel is square-zero. These identities use the original
integral coefficients and hold over any commutative ring.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonArithmeticStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (A : Type*) [CommRing A] (π : A) (m : ℕ)

/-- Restriction retains every original integral representative. -/
@[simp] theorem restriction_mk (a : A) :
    restriction A π m (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ a := rfl

/-- Each original arithmetic coefficient lifts to the next thickening. -/
theorem restriction_surjective : Function.Surjective (restriction A π m) := by
  intro z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩

/-- The full adjacent kernel consists precisely of multiples of the last parameter power. -/
theorem restriction_eq_zero_iff (z : Quotient A π (m + 1)) :
    restriction A π m z = 0 ↔ ∃ w, parameter A π (m + 1) ^ (m + 1) * w = z := by
  constructor
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [restriction_mk, Ideal.Quotient.eq_zero_iff_mem]
    change a ∈ Ideal.span {π} ^ (m + 1) → _
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rintro ⟨b, rfl⟩
    exact ⟨Ideal.Quotient.mk _ b, by rw [map_mul, map_pow]; rfl⟩
  · rintro ⟨w, rfl⟩
    rw [map_mul, map_pow, restriction_parameter, parameter_pow, zero_mul]

/-- The original adjacent coefficient kernel is the last parameter-power ideal. -/
theorem restriction_ker : RingHom.ker (restriction A π m).toRingHom =
    Ideal.span {parameter A π (m + 1)} ^ (m + 1) := by
  rw [Ideal.span_singleton_pow]
  ext z
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  exact (restriction_eq_zero_iff A π m z).trans (exists_congr fun _ ↦ eq_comm)

/-- Every element of the actual adjacent coefficient kernel is square-zero. -/
theorem restriction_kernel_square (z : Quotient A π (m + 1))
    (hz : restriction A π m z = 0) : z ^ 2 = 0 := by
  obtain ⟨w, rfl⟩ := (restriction_eq_zero_iff A π m z).mp hz
  rw [mul_pow, ← pow_mul]
  have he : (m + 1) * 2 = (m + 1 + 1) + m := by omega
  rw [he, pow_add (parameter A π (m + 1)), parameter_pow, zero_mul, zero_mul]

/-- The adjacent coefficient kernel lies in the nilradical. -/
theorem restriction_kernel_le_nilradical :
    RingHom.ker (restriction A π m).toRingHom ≤ nilradical (Quotient A π (m + 1)) := by
  intro z hz
  exact mem_nilradical.mpr ⟨2, restriction_kernel_square A π m z hz⟩

end FLT.Mazur.PolygonArithmeticStages
