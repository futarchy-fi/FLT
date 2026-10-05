/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisiblePointFiberCotangent
public import FLT.GroupScheme.RationalPlacePointPrecision
public import FLT.GroupScheme.PDivisibleCotangentFiniteSets

/-! # Original cotangent coordinates between adjacent positive p-adic precisions -/

@[expose] public noncomputable section
open PadicHodgeTheory
namespace ThreeAdicPlan
variable {p : ℕ} [Fact p.Prime]

/-- Every adjacent positive precision step has square-zero coefficient kernel. -/
theorem rationalPlaceIntegerModPowReduce_squareZero (s : ℕ) (hs : 0 < s) :
    RingHom.ker (rationalPlaceIntegerModPowReduce p (Nat.le_succ s)) ^ 2 = ⊥ := by
  refine integralFactor_ker_pow (by
    rw [← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow]
    exact Ideal.pow_le_pow_right (Nat.le_succ s)) 2 ?_
  rw [← Ideal.span_singleton_pow, ← pow_mul, ← Ideal.span_singleton_pow]
  exact Ideal.pow_le_pow_right (by omega)

/-- One prime annihilates the coefficient kernel of an adjacent precision step. -/
theorem rationalPlaceIntegerModPowReduce_kernel_prime (s : ℕ)
    (a : RingHom.ker (rationalPlaceIntegerModPowReduce p (Nat.le_succ s))) : p • a = 0 := by
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective a.val
  have hmem : b ∈ Ideal.span {(p : 𝓞_ℂ_[p]) ^ s} := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have ha := a.property
    rw [← hb] at ha
    exact ha
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hmem
  apply Subtype.ext
  change p • a.val = 0
  rw [← hb, hc, nsmul_eq_mul, ← map_natCast (Ideal.Quotient.mk _), ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem]
  apply Ideal.mem_span_singleton.mpr
  refine ⟨c, ?_⟩
  rw [pow_succ]
  ring

namespace PDivisibleSystem
variable {height : ℕ}
  (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- The original rational-place cotangents satisfy finite-level representability. -/
local instance precisionCotangentFinite (n : ℕ) : Finite (X.LevelCotangent n) :=
  rationalPlace_levelCotangent_finite X n

/-- The adjacent reduction kernel is exactly the additive original cotangent dual. -/
def rationalPlacePrecisionCotangentEquiv (s : ℕ) (hs : 0 < s) :
    (X.pointColimitMapHom (rationalPlaceIntegerModPowReduce p (Nat.le_succ s))).ker ≃*
      Multiplicative (X.cotangentLimit →ₗ[
        (LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ]
          RingHom.ker (rationalPlaceIntegerModPowReduce p (Nat.le_succ s))) :=
  X.pointKernelCotangentMulEquiv _ (rationalPlaceIntegerModPowReduce_squareZero s hs) 1
    (by simpa only [pow_one] using rationalPlaceIntegerModPowReduce_kernel_prime (p := p) s)

/-- Every adjacent positive-precision fiber has coordinates in that same original dual.
The origin is chosen using proved formal smoothness. -/
def rationalPlacePrecisionFiberCotangentEquiv (s : ℕ) (hs : 0 < s)
    (y : X.PointColimit (ComplexIntegerModPow p s)) :
    {x : X.PointColimit (ComplexIntegerModPow p (s + 1)) //
      X.pointColimitMap (rationalPlaceIntegerModPowReduce p (Nat.le_succ s)) x = y} ≃
        (X.cotangentLimit →ₗ[(LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ]
          RingHom.ker (rationalPlaceIntegerModPowReduce p (Nat.le_succ s))) :=
  X.pointFiberCotangentEquivOfSurjective _
    (rationalPlaceIntegerModPowReduce_squareZero s hs) 1
    (by simpa only [pow_one] using rationalPlaceIntegerModPowReduce_kernel_prime (p := p) s)
    (rationalPlaceIntegerModPowReduce_surjective _) (rationalPlaceIntegerModPow_prime_nilpotent _) y

/-- One prime kills each successive original point kernel, independently of its finite stage. -/
theorem rationalPlacePrecisionKernel_pow_prime (s : ℕ) (hs : 0 < s)
    (x : (X.pointColimitMapHom (rationalPlaceIntegerModPowReduce p (Nat.le_succ s))).ker) :
    x ^ p = 1 := by
  apply (X.rationalPlacePrecisionCotangentEquiv s hs).injective
  rw [map_pow, map_one]
  change p • Multiplicative.toAdd (X.rationalPlacePrecisionCotangentEquiv s hs x) = 0
  apply LinearMap.ext
  intro v
  exact rationalPlaceIntegerModPowReduce_kernel_prime (p := p) s _

end PDivisibleSystem
end ThreeAdicPlan
