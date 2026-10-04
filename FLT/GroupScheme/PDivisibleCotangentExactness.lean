/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFlatCotangentKernel
public import FLT.GroupScheme.FiniteFlatCotangentImage
public import FLT.GroupScheme.PDivisibleCotangentArithmetic

/-! # Exact cotangent sequences of the original integral levels -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)

/-- The original coordinate-kernel equation gives the actual right-exact cotangent sequence. -/
theorem cotangentRestriction_ker (m n : ℕ) :
    LinearMap.ker (X.cotangentRestriction (Nat.le_add_right m n)) =
      LinearMap.range (X.cotangentPullback (Nat.le_add_left n m)) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a, ha, rfl⟩ :=
      ((X.inclusion (Nat.le_add_right m n)).cotangentMap_eq_zero_iff
        (X.closed _) x).mp hx
    have ha' : (a : (X.level (m + n)).CoordinateRing) ∈
        HopfAlgebra.augmentationIdeal (X.reduction (Nat.le_add_left n m)) := by
      rw [X.kernel]
      exact ha
    simpa only [AlgHom.augmentationCotangent_of_mem, cotangentPullback] using
      (X.reduction (Nat.le_add_left n m)).cotangent_projection_mem_range ha'
  · rintro x ⟨y, rfl⟩
    obtain ⟨a, rfl⟩ := (X.level n).cotangentIdeal.toCotangent_surjective y
    change (X.inclusion (Nat.le_add_right m n)).cotangentMap
      ((X.reduction (Nat.le_add_left n m)).cotangentMap _) = 0
    rw [ModelHom.cotangentMap_mk, ModelHom.cotangentMap_mk]
    have ha : X.inclusion (Nat.le_add_right m n)
        (X.reduction (Nat.le_add_left n m) (a : (X.level n).CoordinateRing)) = 0 := by
      have hm := Ideal.mem_map_of_mem (X.reduction (Nat.le_add_left n m)).toAlgHom a.property
      change _ ∈ HopfAlgebra.augmentationIdeal _ at hm
      rw [X.kernel] at hm
      exact hm
    convert (X.level m).cotangentIdeal.toCotangent.map_zero using 1
    exact congrArg (X.level m).cotangentIdeal.toCotangent (Subtype.ext ha)

/-- The kernel of a level restriction consists exactly of p^m multiples upstairs. -/
theorem cotangentRestriction_ker_scalar {m n : ℕ} (h : m ≤ n) :
    LinearMap.ker (X.cotangentRestriction h) =
      LinearMap.range (p ^ m • (LinearMap.id : X.LevelCotangent n →ₗ[R] _)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [X.cotangentRestriction_ker, X.cotangentPullback_range]
  simp only [Nat.add_sub_cancel_right]

/-- Vanishing at an earlier level is equivalent to divisibility by that level's p-power. -/
theorem cotangentRestriction_eq_zero_iff {m n : ℕ} (h : m ≤ n)
    (a : X.LevelCotangent n) :
    X.cotangentRestriction h a = 0 ↔ ∃ b : X.LevelCotangent n, p ^ m • b = a := by
  change a ∈ LinearMap.ker (X.cotangentRestriction h) ↔ _
  rw [X.cotangentRestriction_ker_scalar]
  rfl

end ThreeAdicPlan.PDivisibleSystem
