/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlaceThickening
public import FLT.GroupScheme.PDivisibleFormalSmoothness

/-! # Surjective positive-precision reductions of the original point functor -/

@[expose] public noncomputable section
open PadicHodgeTheory
namespace ThreeAdicPlan
variable {p : ℕ} [Fact p.Prime]

/-- Original-base residue reduction is the identity at equal precision. -/
theorem rationalPlaceIntegerModPowReduce_refl (s : ℕ) :
    rationalPlaceIntegerModPowReduce p (le_refl s) = AlgHom.id _ _ := by
  ext x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- Original-base residue reductions compose on the original coefficients. -/
theorem rationalPlaceIntegerModPowReduce_comp {r s t : ℕ} (h : r ≤ s) (k : s ≤ t) :
    (rationalPlaceIntegerModPowReduce p h).comp (rationalPlaceIntegerModPowReduce p k) =
      rationalPlaceIntegerModPowReduce p (h.trans k) := by
  ext x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- Residue precision reduction is surjective as a coefficient map. -/
theorem rationalPlaceIntegerModPowReduce_surjective {s t : ℕ} (h : s ≤ t) :
    Function.Surjective (rationalPlaceIntegerModPowReduce p h) :=
  Ideal.Quotient.factor_surjective (by
    rw [← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow]
    exact Ideal.pow_le_pow_right h)

/-- The actual prime is nilpotent at every finite residue precision. -/
theorem rationalPlaceIntegerModPow_prime_nilpotent (s : ℕ) :
    IsNilpotent (p : ComplexIntegerModPow p s) := by
  refine ⟨s, ?_⟩
  rw [← map_natCast (Ideal.Quotient.mk _), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- Every reduction to positive precision has nilpotent kernel. -/
theorem rationalPlaceIntegerModPowReduce_ker_nilpotent {s t : ℕ}
    (h : s ≤ t) (hs : 0 < s) :
    IsNilpotent (RingHom.ker (rationalPlaceIntegerModPowReduce p h)) := by
  refine ⟨t, integralFactor_ker_pow (by
    rw [← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow]
    exact Ideal.pow_le_pow_right h) t ?_⟩
  rw [← Ideal.span_singleton_pow, ← pow_mul, ← Ideal.span_singleton_pow]
  exact Ideal.pow_le_pow_right (by nlinarith)

variable {height : ℕ}
  (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- Formal smoothness lifts every original colimit point across any positive precision gap. -/
theorem rationalPlacePointPrecision_surjective {s t : ℕ} (h : s ≤ t) (hs : 0 < s) :
    Function.Surjective (X.pointColimitMap (rationalPlaceIntegerModPowReduce p h)) :=
  X.pointColimitMap_surjective_nilpotent _
    (rationalPlaceIntegerModPowReduce_surjective h)
    (rationalPlaceIntegerModPowReduce_ker_nilpotent h hs)
    (rationalPlaceIntegerModPow_prime_nilpotent t)

end ThreeAdicPlan
