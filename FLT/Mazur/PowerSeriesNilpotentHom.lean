/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PowerSeriesTruncatedPolynomial

/-!
# Algebra maps with nilpotent parameter image

An algebra map out of power series whose parameter image is nilpotent is
determined by that image. No topology on the target algebra is required.
-/

@[expose] public noncomputable section

open Polynomial

namespace FLT.Mazur.PowerSeriesNilpotentHom

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- A nilpotent parameter kills the tail of every power series. -/
theorem apply_eq_trunc (f : PowerSeries R →ₐ[R] A) {n : ℕ}
    (hn : f PowerSeries.X ^ n = 0) (s : PowerSeries R) :
    f s = f (PowerSeries.trunc n s : PowerSeries R) := by
  conv_lhs => rw [PowerSeries.eq_X_pow_mul_shift_add_trunc n s]
  rw [map_add, map_mul, map_pow, hn, zero_mul, zero_add]

/-- Maps with a nilpotent parameter image agree once they agree on that image. -/
theorem ext (f g : PowerSeries R →ₐ[R] A) (hf : IsNilpotent (f PowerSeries.X))
    (h : f PowerSeries.X = g PowerSeries.X) : f = g := by
  obtain ⟨n, hn⟩ := hf
  have hp : f.comp (Polynomial.coeToPowerSeries.algHom R) =
      g.comp (Polynomial.coeToPowerSeries.algHom R) := by
    apply Polynomial.algHom_ext
    simpa [Polynomial.coeToPowerSeries.algHom_apply] using h
  ext s
  rw [apply_eq_trunc f hn, apply_eq_trunc g (h ▸ hn)]
  simpa [Polynomial.coeToPowerSeries.algHom_apply] using
    DFunLike.congr_fun hp (PowerSeries.trunc n s)

end FLT.Mazur.PowerSeriesNilpotentHom
