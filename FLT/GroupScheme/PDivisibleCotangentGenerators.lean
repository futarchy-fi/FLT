/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleCotangentExactness
public import FLT.GroupScheme.PDivisibleCotangentSurjective
public import FLT.GroupScheme.FiniteFlatCotangentFinite
public import FLT.Mathlib.RingTheory.NilpotentGeneratorLifting
public import Mathlib.RingTheory.Finiteness.Cardinality

/-! # A single finite family generates all original cotangent levels -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)

/-- Generating level one by limit vectors suffices to generate every actual level. -/
theorem cotangentEval_surjective_of_level_one {M : Type*} [AddCommGroup M] [Module R M]
    (f : M →ₗ[R] X.cotangentLimit)
    (hf : Function.Surjective ((X.cotangentEval 1).comp f)) (n : ℕ) :
    Function.Surjective ((X.cotangentEval n).comp f) := by
  apply LinearMap.surjective_of_scalar_nilpotent _ (p : R) n
  · intro a
    simpa only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] using X.cotangent_pow_smul_eq_zero n a
  · intro a
    by_cases hn : 1 ≤ n
    · obtain ⟨b, hb⟩ := hf (X.cotangentRestriction hn a)
      have hz : X.cotangentRestriction hn (a - X.cotangentEval n (f b)) = 0 := by
        rw [map_sub, X.cotangentEval_restriction]
        exact sub_eq_zero.mpr hb.symm
      obtain ⟨c, hc⟩ := (X.cotangentRestriction_eq_zero_iff hn _).mp hz
      refine ⟨b, c, ?_⟩
      change X.cotangentEval n (f b) + (p : R) • c = a
      rw [pow_one] at hc
      rw [Nat.cast_smul_eq_nsmul, hc]
      abel
    · have hn' : n = 0 := by omega
      subst n
      exact ⟨0, 0, by simp only [map_zero, smul_zero, add_zero, X.cotangent_zero_eq_zero a]⟩

/-- One finite family of actual limit vectors generates every finite-level cotangent. -/
theorem exists_cotangent_level_generators :
    ∃ d : ℕ, ∃ f : (Fin d → R) →ₗ[R] X.cotangentLimit,
      ∀ n, Function.Surjective ((X.cotangentEval n).comp f) := by
  obtain ⟨d, g, hg⟩ := Module.Finite.exists_fin' R (X.LevelCotangent 1)
  let b := Pi.basisFun R (Fin d)
  choose v hv using fun i ↦ X.cotangentEval_surjective 1 (g (b i))
  let f := b.constr R v
  have he : (X.cotangentEval 1).comp f = g := by
    apply b.ext
    intro i
    simpa only [LinearMap.comp_apply, f, Module.Basis.constr_basis] using hv i
  refine ⟨d, f, X.cotangentEval_surjective_of_level_one f ?_⟩
  rw [he]
  exact hg

end ThreeAdicPlan.PDivisibleSystem
