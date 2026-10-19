/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.VeluIntegralAway
public import FLT.Mazur.RationalPadicIntegerSubring
public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction

/-!
# Actual Frey target equations over rational local rings

Away from the kernel prime, the canonical target equation is integral over
the rational local coefficient ring. Completing that very equation gives
an integral p-adic model with the original generic fiber, without a change
of variables. Minimality is a separate question.
-/

@[expose] public section

namespace FreyPackage

open WeierstrassCurve FLT.Mazur

variable {P : FreyPackage} {E : WeierstrassCurve ℚ}

/-- The canonical target has an integral equation at every distinct rational prime. -/
theorem IsVeluTarget.exists_rational_local_model (h : P.IsVeluTarget E)
    (q : ℕ) [Fact q.Prime] (hqp : q ≠ P.p) :
    ∃ U : WeierstrassCurve (rationalPadicIntegerSubring q),
      U.map (algebraMap (rationalPadicIntegerSubring q) ℚ) = E := by
  apply h.exists_integral_model
  exact rationalPadicIntegerSubring_isUnit_nat q
    ((Nat.coprime_primes (Fact.out : q.Prime) P.pp).mpr hqp)

/-- Completion of the rational integral equation recovers the actual target over ℚ_q. -/
theorem IsVeluTarget.exists_compatible_padic_integral_model (h : P.IsVeluTarget E)
    (q : ℕ) [Fact q.Prime] (hqp : q ≠ P.p) :
    ∃ U : WeierstrassCurve (rationalPadicIntegerSubring q),
      U.map (algebraMap (rationalPadicIntegerSubring q) ℚ) = E ∧
      (U.map (rationalPadicIntegerMap q)).map
          (algebraMap (padicIntegerSubring q) ℚ_[q]) = E.map (algebraMap ℚ ℚ_[q]) := by
  obtain ⟨U, hU⟩ := h.exists_rational_local_model q hqp
  refine ⟨U, hU, ?_⟩
  rw [WeierstrassCurve.map_map, rationalPadicIntegerMap_comp,
    ← WeierstrassCurve.map_map, hU]

/-- The original target equation itself is integral at every prime different from p. -/
theorem IsVeluTarget.padic_isIntegral (h : P.IsVeluTarget E)
    (q : ℕ) [Fact q.Prime] (hqp : q ≠ P.p) :
    WeierstrassCurve.IsIntegral (padicIntegerSubring q) (E.map (algebraMap ℚ ℚ_[q])) := by
  obtain ⟨U, _, hU⟩ := h.exists_compatible_padic_integral_model q hqp
  exact ⟨U.map (rationalPadicIntegerMap q), hU.symm⟩

end FreyPackage
