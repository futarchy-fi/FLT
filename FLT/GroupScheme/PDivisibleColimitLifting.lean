/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisiblePointColimit

/-! # The exact finite-level criterion for surjectivity on the point colimit -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)
  {B C : Type} [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]

/-- Equality in the colimit is equality after the two specified inclusions. -/
theorem pointColimitMk_eq_iff {m n : ℕ}
    (x : (X.level m).CoordinateRing →ₐ[R] B)
    (y : (X.level n).CoordinateRing →ₐ[R] B) :
    X.pointColimitMk m x = X.pointColimitMk n y ↔
      ∃ (k : ℕ) (hm : m ≤ k) (hn : n ≤ k), X.pointInclusion hm x = X.pointInclusion hn y :=
  Quotient.eq

/-- Surjectivity is exactly lifting each point at some higher original level.
This criterion makes no claim that either side holds for a thickening. -/
theorem pointColimitMap_surjective_iff (q : B →ₐ[R] C) :
    Function.Surjective (X.pointColimitMap q) ↔
      ∀ n (x : (X.level n).CoordinateRing →ₐ[R] C),
        ∃ (m : ℕ) (h : n ≤ m) (y : (X.level m).CoordinateRing →ₐ[R] B),
          q.comp y = x.comp (X.inclusion h).toAlgHom := by
  constructor
  · intro hs n x
    obtain ⟨z, hz⟩ := hs (X.pointColimitMk n x)
    obtain ⟨i, y, rfl⟩ := DirectLimit.exists_eq_mk _ z
    obtain ⟨m, hi, hn, he⟩ := (X.pointColimitMk_eq_iff (q.comp y) x).mp hz
    exact ⟨m, hn, X.pointInclusion hi y, he⟩
  · intro hs z
    obtain ⟨n, x, rfl⟩ := DirectLimit.exists_eq_mk _ z
    obtain ⟨m, h, y, hy⟩ := hs n x
    refine ⟨X.pointColimitMk m y, ?_⟩
    rw [X.pointColimitMap_mk, hy]
    exact X.pointColimitMk_inclusion h x

/-- Lifting through two successive test-algebra maps composes on the same colimit. -/
theorem pointColimitMap_surjective_comp {D : Type} [CommRing D] [Algebra R D]
    (q : B →ₐ[R] C) (s : C →ₐ[R] D)
    (hq : Function.Surjective (X.pointColimitMap q))
    (hs : Function.Surjective (X.pointColimitMap s)) :
    Function.Surjective (X.pointColimitMap (s.comp q)) := by
  intro z
  obtain ⟨y, rfl⟩ := hs z
  obtain ⟨x, rfl⟩ := hq y
  exact ⟨x, X.pointColimitMap_comp q s x⟩

end ThreeAdicPlan.PDivisibleSystem
