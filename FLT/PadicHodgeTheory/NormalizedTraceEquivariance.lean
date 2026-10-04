/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.FieldTheory.NormalizedTrace

/-! # Equivariance of the actual normalized trace under compatible field automorphisms -/

@[expose] public noncomputable section
namespace PadicHodgeTheory

/-- Compatible automorphisms of base and extension commute with the actual normalized trace. -/
theorem normalizedTrace_equivariant (F K : Type*) [Field F] [Field K] [CharZero F]
    [Algebra F K] [Algebra.IsIntegral F K] (f : F ≃+* F) (g : K ≃+* K)
    (h : (algebraMap F K).comp f = g.toRingHom.comp (algebraMap F K)) (x : K) :
    f (Algebra.normalizedTrace F K x) = Algebra.normalizedTrace F K (g x) := by
  rw [Algebra.normalizedTrace_minpoly, Algebra.normalizedTrace_minpoly,
    ← minpoly.map_eq_of_equiv_equiv h x, Polynomial.natDegree_map,
    Polynomial.nextCoeff_map f.injective]
  simp only [smul_eq_mul, map_mul, map_inv₀, map_natCast, map_neg, RingEquiv.coe_toRingHom]

end PadicHodgeTheory
