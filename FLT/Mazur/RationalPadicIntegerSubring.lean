/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PadicValuationRing
public import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Rational coefficients integral at a p-adic place

Pull the actual p-adic valuation ring back to the rationals. This gives an
integrally closed local coefficient ring with fraction field ℚ and a concrete
map to the p-adic integers. Primes different from the place are units.
-/

@[expose] public noncomputable section

namespace FLT.Mazur

variable (q : ℕ) [Fact q.Prime]

/-- The rational numbers whose images in ℚ_q are integral. -/
def rationalPadicIntegerSubring : ValuationSubring ℚ :=
  (padicIntegerSubring q).comap (algebraMap ℚ ℚ_[q])

/-- Membership is the ordinary p-adic norm bound on the rational coefficient. -/
theorem mem_rationalPadicIntegerSubring (x : ℚ) :
    x ∈ rationalPadicIntegerSubring q ↔ ‖(algebraMap ℚ ℚ_[q]) x‖ ≤ 1 := Iff.rfl

/-- The concrete inclusion of rational integral coefficients into the complete local ring. -/
def rationalPadicIntegerMap : rationalPadicIntegerSubring q →+* padicIntegerSubring q :=
  { (algebraMap ℚ ℚ_[q]).comp (algebraMap (rationalPadicIntegerSubring q) ℚ) with
    toFun := fun x ↦ ⟨algebraMap ℚ ℚ_[q] x.val, x.property⟩
    map_one' := Subtype.ext (map_one _)
    map_mul' := fun x y ↦ Subtype.ext (map_mul _ x.val y.val)
    map_zero' := Subtype.ext (map_zero _)
    map_add' := fun x y ↦ Subtype.ext (map_add _ x.val y.val) }

/-- Completing a rational integral coefficient agrees with its original rational embedding. -/
theorem rationalPadicIntegerMap_comp :
    (algebraMap (padicIntegerSubring q) ℚ_[q]).comp (rationalPadicIntegerMap q) =
      (algebraMap ℚ ℚ_[q]).comp (algebraMap (rationalPadicIntegerSubring q) ℚ) := rfl

/-- Every natural number prime to the place is a unit in the rational coefficient ring. -/
theorem rationalPadicIntegerSubring_isUnit_nat {n : ℕ} (hn : q.Coprime n) :
    IsUnit (n : rationalPadicIntegerSubring q) := by
  have hn0 : (n : ℚ) ≠ 0 := by
    have h : n ≠ 0 := by
      intro hz
      have hq : q = 1 := by simpa [hz] using hn
      exact (Fact.out : q.Prime).ne_one hq
    exact_mod_cast h
  have hi : (n : ℚ)⁻¹ ∈ rationalPadicIntegerSubring q := by
    rw [mem_rationalPadicIntegerSubring, map_inv₀, map_natCast, norm_inv,
      Padic.norm_natCast_eq_one_iff.mpr hn, inv_one]
  refine ⟨⟨n, ⟨(n : ℚ)⁻¹, hi⟩, ?_, ?_⟩, rfl⟩
  · apply Subtype.ext
    exact mul_inv_cancel₀ hn0
  · apply Subtype.ext
    exact inv_mul_cancel₀ hn0

end FLT.Mazur
