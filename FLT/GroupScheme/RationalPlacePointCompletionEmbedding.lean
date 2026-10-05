/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlaceCompletedPoints
public import FLT.GroupScheme.PDivisiblePointColimitTorsion
public import FLT.PadicHodgeTheory.ComplexIntegerAdic

/-! # Original integral torsion points embed into the completed point group -/

@[expose] public noncomputable section
open PadicHodgeTheory
namespace ThreeAdicPlan.PDivisibleSystem
variable {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- Equality of the completed points detects every original integral coordinate. -/
theorem rationalPlacePointCompletion_injective :
    Function.Injective X.rationalPlacePointCompletion := by
  intro x y
  induction x, y using DirectLimit.induction₂ (fun _ _ h ↦ X.pointInclusion h) with
  | ih n x y =>
    intro h
    apply congrArg (X.pointColimitMk n)
    apply DFunLike.ext'
    apply IsHausdorff.StrictMono.funext' (Ideal.span {(p : 𝓞_ℂ_[p])})
      (a := fun s : ℕ ↦ s + 1) (by intro s t h; exact Nat.add_lt_add_right h 1)
    intro s
    have hs := congrArg (X.rationalPlaceCompletedPointEval s) h
    have he := X.pointColimitMk_injective n hs
    rw [Ideal.span_singleton_pow]
    exact fun r ↦ AlgHom.congr_fun he r

/-- Original finite-stage points retain their exact p-power annihilator bound after completion. -/
theorem rationalPlacePointCompletion_mk_pow_prime (n : ℕ)
    (x : (X.level n).CoordinateRing →ₐ[(LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ]
      𝓞_ℂ_[p]) :
    X.rationalPlacePointCompletion (X.pointColimitMk n x) ^ (p ^ n) = 1 := by
  rw [← map_pow, X.pointColimitMk_pow_prime, map_one]

/-- Every point coming from the original integral point colimit is p-primary torsion. -/
theorem rationalPlacePointCompletion_exists_pow_prime_eq_one (x : X.PointColimit 𝓞_ℂ_[p]) :
    ∃ n : ℕ, X.rationalPlacePointCompletion x ^ (p ^ n) = 1 := by
  obtain ⟨n, hn⟩ := X.pointColimit_exists_pow_prime_eq_one x
  exact ⟨n, by rw [← map_pow, hn, map_one]⟩

end ThreeAdicPlan.PDivisibleSystem
