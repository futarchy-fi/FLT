/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleCotangentFunctionalLifting
public import FLT.Mathlib.RingTheory.PrincipalPowerTorsion
public import Mathlib.Algebra.Module.Torsion.Basic

/-! # Multiplication by p is injective on the original cotangent inverse limit -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height) [∀ n, Finite (X.LevelCotangent n)]

/-- Infinitesimal lifting rules out p-torsion in the original cotangent limit. -/
theorem cotangentLimit_eq_zero_of_prime_smul (hp : (p : R) ≠ 0)
    (x : X.cotangentLimit) (hx : (p : R) • x = 0) : x = 0 := by
  apply X.cotangentLimit_ext
  intro n
  let S := R ⧸ Ideal.span {(p : R) ^ (n + 1)}
  have ht : Module.IsTorsionBy R (X.LevelCotangent (n + 1)) ((p : R) ^ (n + 1)) := by
    intro a
    simpa only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] using
      X.cotangent_pow_smul_eq_zero (n + 1) a
  let : Module S (X.LevelCotangent (n + 1)) := ht.module
  let : IsScalarTower R S (X.LevelCotangent (n + 1)) :=
    Module.IsTorsionBySet.isScalarTower _
  let : Module.Finite S (X.LevelCotangent (n + 1)) :=
    Module.Finite.of_restrictScalars_finite R S _
  obtain ⟨d, f, hf⟩ := Module.Finite.exists_fin' S (X.LevelCotangent (n + 1))
  have hS : IsNilpotent (p : S) := by
    refine ⟨n + 1, ?_⟩
    change (Ideal.Quotient.mk _ (p : R)) ^ (n + 1) = 0
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_singleton _)
  obtain ⟨g, hg⟩ := X.exists_cotangent_functional_lift hS f hf (X.cotangentEval (n + 1))
  have hgx : (p : R) • g x = 0 := by rw [← map_smul, hx, map_zero]
  obtain ⟨y, hy⟩ := Ideal.Quotient.exists_pow_smul_of_smul_eq_zero (p : R) hp n (g x) hgx
  have he : X.cotangentEval (n + 1) x = (p : R) ^ n • f y := by
    rw [← LinearMap.congr_fun hg x]
    change f (g x) = _
    rw [← hy]
    exact (f.restrictScalars R).map_smul _ _
  rw [← X.cotangentEval_restriction (Nat.le_succ n) x, he, map_smul]
  simpa only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, map_zero] using
    X.cotangent_pow_smul_eq_zero n (X.cotangentRestriction (Nat.le_succ n) (f y))

/-- The original limit has regular multiplication by p. -/
theorem cotangentLimit_prime_smul_injective (hp : (p : R) ≠ 0) :
    Function.Injective (fun x : X.cotangentLimit ↦ (p : R) • x) := by
  intro x y h
  apply sub_eq_zero.mp
  apply X.cotangentLimit_eq_zero_of_prime_smul hp
  change (p : R) • x = (p : R) • y at h
  rw [smul_sub, h, sub_self]

end ThreeAdicPlan.PDivisibleSystem
