/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlacePrecisionCotangent
public import FLT.GroupScheme.RationalPlaceCompletedPointLifting
public import FLT.GroupScheme.PDivisiblePointColimitTorsion

/-! # Cotangent directions of the actual completed point filtration -/

@[expose] public noncomputable section
open PadicHodgeTheory
namespace ThreeAdicPlan.PDivisibleSystem
variable {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- Evaluate a completed point trivial at precision s+1 in the next original residue kernel. -/
def rationalPlaceCompletedPointStep (s : ℕ) :
    (X.rationalPlaceCompletedPointEval s).ker →*
      (X.pointColimitMapHom (rationalPlaceIntegerModPowReduce p (Nat.le_succ (s + 1)))).ker where
  toFun x := ⟨X.rationalPlaceCompletedPointEval (s + 1) x.val, by
    change X.pointColimitMap _ (X.rationalPlaceCompletedPointEval (s + 1) x.val) = 1
    exact (X.rationalPlaceCompletedPointEval_reduce x.val (Nat.le_succ s)).trans x.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x.val y.val)

/-- Every next-precision direction is realized by an actual completed point in the neighborhood. -/
theorem rationalPlaceCompletedPointStep_surjective (s : ℕ) :
    Function.Surjective (X.rationalPlaceCompletedPointStep s) := by
  intro y
  obtain ⟨x, hx⟩ := X.rationalPlaceCompletedPointEval_surjective (s + 1) y.val
  have hs : X.rationalPlaceCompletedPointEval s x = 1 := by
    rw [← X.rationalPlaceCompletedPointEval_reduce x (Nat.le_succ s), hx]
    exact y.property
  exact ⟨⟨x, hs⟩, Subtype.ext hx⟩

/-- The cotangent direction of a completed point is computed in the original adjacent kernel. -/
def rationalPlaceCompletedPointCotangent (s : ℕ) :
    (X.rationalPlaceCompletedPointEval s).ker →*
      Multiplicative (X.cotangentLimit →ₗ[
        (LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ]
          RingHom.ker (rationalPlaceIntegerModPowReduce p (Nat.le_succ (s + 1)))) :=
  (X.rationalPlacePrecisionCotangentEquiv (s + 1) (Nat.zero_lt_succ s)).toMonoidHom.comp
    (X.rationalPlaceCompletedPointStep s)

/-- All original cotangent functionals occur as successive directions of completed points. -/
theorem rationalPlaceCompletedPointCotangent_surjective (s : ℕ) :
    Function.Surjective (X.rationalPlaceCompletedPointCotangent s) :=
  (X.rationalPlacePrecisionCotangentEquiv (s + 1) (Nat.zero_lt_succ s)).surjective.comp
    (X.rationalPlaceCompletedPointStep_surjective s)

/-- A direction is zero precisely when the completed point is trivial at the next precision. -/
theorem rationalPlaceCompletedPointCotangent_eq_one_iff (s : ℕ)
    (x : (X.rationalPlaceCompletedPointEval s).ker) :
    X.rationalPlaceCompletedPointCotangent s x = 1 ↔
      X.rationalPlaceCompletedPointEval (s + 1) x.val = 1 := by
  change X.rationalPlacePrecisionCotangentEquiv (s + 1) (Nat.zero_lt_succ s)
    (X.rationalPlaceCompletedPointStep s x) = 1 ↔ _
  rw [map_eq_one_iff _ (X.rationalPlacePrecisionCotangentEquiv
    (s + 1) (Nat.zero_lt_succ s)).injective]
  exact Subtype.ext_iff

/-- Multiplication by the actual prime raises the identity precision by one, uniformly. -/
theorem rationalPlaceCompletedPoint_pow_prime_precision (s : ℕ)
    (x : X.RationalPlaceCompletedPoints) (hx : X.rationalPlaceCompletedPointEval s x = 1) :
    X.rationalPlaceCompletedPointEval (s + 1) (x ^ p) = 1 := by
  have h := X.rationalPlacePrecisionKernel_pow_prime (s + 1) (Nat.zero_lt_succ s)
    (X.rationalPlaceCompletedPointStep s ⟨x, hx⟩)
  exact (map_pow (X.rationalPlaceCompletedPointEval (s + 1)) x p).trans
    (congrArg Subtype.val h)

/-- Iterated original p-multiplication gains the number of iterations in residue precision. -/
theorem rationalPlaceCompletedPoint_pow_prime_pow_precision (s n : ℕ)
    (x : X.RationalPlaceCompletedPoints) (hx : X.rationalPlaceCompletedPointEval s x = 1) :
    X.rationalPlaceCompletedPointEval (s + n) (x ^ (p ^ n)) = 1 := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    simpa only [Nat.add_succ, pow_succ p n, pow_mul] using
      X.rationalPlaceCompletedPoint_pow_prime_precision (s + n) (x ^ (p ^ n)) ih

/-- One initial residue annihilator controls every higher precision with a linear bound. -/
theorem rationalPlaceCompletedPoint_exists_uniform_precision (x : X.RationalPlaceCompletedPoints) :
    ∃ m : ℕ, ∀ s : ℕ, X.rationalPlaceCompletedPointEval s (x ^ (p ^ (m + s))) = 1 := by
  obtain ⟨m, hm⟩ := X.pointColimit_exists_pow_prime_eq_one (X.rationalPlaceCompletedPointEval 0 x)
  have hzero : X.rationalPlaceCompletedPointEval 0 (x ^ (p ^ m)) = 1 := by
    rw [map_pow, hm]
  refine ⟨m, fun s ↦ ?_⟩
  rw [pow_add p m s, pow_mul x (p ^ m) (p ^ s)]
  exact Eq.mp (congrArg (fun t ↦ X.rationalPlaceCompletedPointEval t
    ((x ^ (p ^ m)) ^ (p ^ s)) = 1) (Nat.zero_add s))
      (X.rationalPlaceCompletedPoint_pow_prime_pow_precision 0 s (x ^ (p ^ m)) hzero)

end ThreeAdicPlan.PDivisibleSystem
