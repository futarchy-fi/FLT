/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFlatSquareZeroLifting

/-! # Square-zero lifting of p-power multiplication in the original level system

These are lifts of multiplication and of its specified transition composites.
They do not assert lifting an arbitrary point along the level inclusions.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K B C : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] [CommRing B] [CommRing C]
  [Algebra R B] [Algebra R C] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)

/-- The original level's p-power multiple lifts across any eligible square-zero thickening. -/
theorem exists_pow_point_lift (q : B →ₐ[R] C) (hq : Function.Surjective q)
    (hJ : RingHom.ker q ^ 2 = ⊥) (n r : ℕ)
    (hr : ∀ b ∈ RingHom.ker q, p ^ r • b = 0)
    (x : (X.level n).CoordinateRing →ₐ[R] C) :
    ∃ y : (X.level n).CoordinateRing →ₐ[R] B,
      q.comp y = x.comp ((X.level n).multiply (p ^ r)).toAlgHom :=
  (X.level n).exists_multiply_lift q hq hJ (p ^ r) hr x

/-- The lower-level inclusion/reduction composite has a lift with the original coordinate maps. -/
theorem exists_inclusion_reduction_point_lift (q : B →ₐ[R] C) (hq : Function.Surjective q)
    (hJ : RingHom.ker q ^ 2 = ⊥) {m n : ℕ} (h : m ≤ n)
    (hr : ∀ b ∈ RingHom.ker q, p ^ (n - m) • b = 0)
    (x : (X.level m).CoordinateRing →ₐ[R] C) :
    ∃ y : (X.level m).CoordinateRing →ₐ[R] B,
      q.comp y = (x.comp (X.inclusion h).toAlgHom).comp (X.reduction h).toAlgHom := by
  obtain ⟨y, hy⟩ := X.exists_pow_point_lift q hq hJ m (n - m) hr x
  refine ⟨y, ?_⟩
  rw [hy, ← X.inclusion_reduction h]
  rfl

/-- The higher-level reduction/inclusion composite has a lift on that same original level. -/
theorem exists_reduction_inclusion_point_lift (q : B →ₐ[R] C) (hq : Function.Surjective q)
    (hJ : RingHom.ker q ^ 2 = ⊥) {m n : ℕ} (h : m ≤ n)
    (hr : ∀ b ∈ RingHom.ker q, p ^ (n - m) • b = 0)
    (x : (X.level n).CoordinateRing →ₐ[R] C) :
    ∃ y : (X.level n).CoordinateRing →ₐ[R] B,
      q.comp y = (x.comp (X.reduction h).toAlgHom).comp (X.inclusion h).toAlgHom := by
  obtain ⟨y, hy⟩ := X.exists_pow_point_lift q hq hJ n (n - m) hr x
  refine ⟨y, ?_⟩
  rw [hy, ← X.reduction_inclusion h]
  rfl

end ThreeAdicPlan.PDivisibleSystem
