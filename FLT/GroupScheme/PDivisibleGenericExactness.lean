/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleTateEvaluationSurjective
public import FLT.GroupScheme.FiniteGroupKernelCard
public import FLT.GroupScheme.ModelKernelComposition
public import FLT.GroupScheme.RaynaudAugmentationRank

/-! # Exactness of the original generic p-divisible levels -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)

/-- The specified closed inclusion is injective on the original geometric points. -/
theorem inclusion_points_injective {m n : ℕ} (h : m ≤ n) :
    Function.Injective (genericHom (X.inclusion h)) := by
  intro x y he
  obtain ⟨a, rfl⟩ := (X.level m).points_bijective.2 x
  obtain ⟨b, rfl⟩ := (X.level m).points_bijective.2 y
  rw [genericHom_points, genericHom_points] at he
  have he' := (X.level n).points_bijective.1 he
  congr 1
  apply Additive.toMul.injective
  apply (Bialgebra.restrictPoints R K (AlgebraicClosure K) _).injective
  ext c
  obtain ⟨d, rfl⟩ := X.closed h c
  exact congrArg (fun z ↦ z.toMul (1 ⊗ₜ[R] d)) he'

/-- The actual consecutive inclusion and quotient have zero composite. -/
theorem transition_points_zero (m n : ℕ) (x : (X.level m).Points) :
    genericHom (X.reduction (Nat.le_add_left n m))
      (genericHom (X.inclusion (Nat.le_add_right m n)) x) = 0 := by
  have h := ModelHom.comp_eq_zero_of_augmentation_le
    (X.inclusion (Nat.le_add_right m n)) (X.reduction (Nat.le_add_left n m)) (X.kernel m n).le
  have he := congrArg (fun f ↦ genericHom f x) h
  simpa only [genericHom_comp, ModelHom.genericHom_zero] using he

/-- The prescribed geometric sequence is exact, by its integral ranks and maps. -/
theorem transition_points_exact (m n : ℕ) (x : (X.level (m + n)).Points) :
    genericHom (X.reduction (Nat.le_add_left n m)) x = 0 ↔
      ∃ a, genericHom (X.inclusion (Nat.le_add_right m n)) a = x := by
  apply AddMonoidHom.exact_of_card_mul
    (genericHom (X.inclusion (Nat.le_add_right m n))).toAddMonoidHom
    (genericHom (X.reduction (Nat.le_add_left n m))).toAddMonoidHom
    (X.inclusion_points_injective _) (X.reduction_points_surjective _)
    (X.transition_points_zero m n)
  rw [← FF.coordinate_finrank, ← FF.coordinate_finrank, ← FF.coordinate_finrank,
    X.rank, X.rank, X.rank, Nat.add_mul, pow_add]

/-- A finite reduction kernel consists exactly of the corresponding p-power multiples. -/
theorem reduction_points_eq_zero_iff {m n : ℕ} (h : m ≤ n) (x : (X.level n).Points) :
    genericHom (X.reduction h) x = 0 ↔ ∃ y : (X.level n).Points, p ^ m • y = x := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_comm] at hk
  subst n
  rw [X.transition_points_exact]
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨b, rfl⟩ := X.reduction_points_surjective (Nat.le_add_right k m) a
    refine ⟨b, ?_⟩
    rw [← genericHom_comp, X.reduction_inclusion, FF.genericHom_multiply]
    simp
  · rintro ⟨y, rfl⟩
    refine ⟨genericHom (X.reduction (Nat.le_add_right k m)) y, ?_⟩
    rw [← genericHom_comp, X.reduction_inclusion, FF.genericHom_multiply]
    simp
end ThreeAdicPlan.PDivisibleSystem
