/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticStageCoefficients
public import Mathlib.AlgebraicGeometry.Scheme

/-!
# Every arithmetic input is supported over the original special fiber

Any affine input with the actual arithmetic coefficient map contains the
uniformizer in its image prime. No reducedness or flatness is needed.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.PolygonArithmeticStages
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (π : R) (m : ℕ) {T : Scheme.{u}}
local notation "Q" => Quotient R π m
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "s" => Spec.map (CommRingCat.ofHom (algebraMap R S))

/-- Compatibility with the actual arithmetic base forces every image prime onto the closed fiber. -/
theorem spectrumInput_parameter_mem (x : T ⟶ Spec (.of S)) (t : T ⟶ Spec (.of Q))
    (h : x ≫ s = t ≫ q) (p : T) : algebraMap R S π ∈ (x p).asIdeal := by
  have hx : s (x p) = q (t p) := congrArg (fun f : T ⟶ Spec (.of R) => f p) h
  change π ∈ (s (x p)).asIdeal
  rw [hx]
  exact nilpotent_iff_mem_prime.mp ⟨m + 1, parameter_pow R π m⟩ (t p).asIdeal (t p).isPrime

end FLT.Mazur.PolygonArithmeticStages
