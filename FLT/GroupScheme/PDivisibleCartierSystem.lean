/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleCartierTransitions
public import FLT.GroupScheme.HopfExactPairDuality

/-! # The Cartier-dual p-divisible system on the original local dual models -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] [CharZero K]
  {p height : ℕ} [Fact p.Prime] (X : PDivisibleSystem R K p height)

/-- The dual quotient coordinate map is faithfully flat over the actual local base. -/
theorem dualReduction_faithfullyFlat {m n : ℕ} (h : m ≤ n) :
    (X.dualReduction h).toAlgHom.toRingHom.FaithfullyFlat :=
  HopfAlgebra.CartierDual.bialgMap_faithfullyFlat_of_surjective _ (X.closed h)

/-- Exactness of the original integral sequence gives closed dual inclusions. -/
theorem dualInclusion_closed_add (m n : ℕ) :
    Function.Surjective (X.dualInclusion (Nat.le_add_left n m)) :=
  HopfAlgebra.ExactPair.dual_closed (X.inclusion (Nat.le_add_right m n))
    (X.reduction (Nat.le_add_left n m)) (X.closed _) (X.kernel m n) (X.faithfullyFlat _)

/-- Every original transposed reduction is a closed inclusion of dual models. -/
theorem dualInclusion_closed {m n : ℕ} (h : m ≤ n) :
    Function.Surjective (X.dualInclusion h) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have hk : ∀ t, k + m = t → ∀ ht : m ≤ t,
      Function.Surjective (X.dualInclusion ht) := by
    intro t he
    subst t
    intro ht
    exact X.dualInclusion_closed_add k m
  exact hk _ (Nat.add_comm _ _) h

/-- The dual sequence satisfies its actual augmentation-kernel equation. -/
theorem dual_kernel (m n : ℕ) :
    HopfAlgebra.augmentationIdeal (X.dualReduction (Nat.le_add_left n m)) =
      RingHom.ker (X.dualInclusion (Nat.le_add_right m n)).toAlgHom.toRingHom := by
  have h : ∀ t, n + m = t → ∀ (hn : n ≤ t) (hm : m ≤ t),
      HopfAlgebra.augmentationIdeal (X.dualReduction hn) =
        RingHom.ker (X.dualInclusion hm).toAlgHom.toRingHom := by
    intro t he
    subst t
    intro hn hm
    exact HopfAlgebra.ExactPair.dual_kernel (X.inclusion hn) (X.reduction hm)
      (X.closed _) (X.kernel n m) (X.faithfullyFlat _)
  exact h _ (Nat.add_comm _ _) _ _

/-- The original Cartier-dual levels, with transposed transitions, form a p-divisible system. -/
def cartierDual : PDivisibleSystem R K p height where
  level n := (X.level n).cartierDual
  inclusion := X.dualInclusion
  reduction := X.dualReduction
  inclusion_refl := X.dualInclusion_refl
  reduction_refl := X.dualReduction_refl
  inclusion_comp := X.dualInclusion_comp
  reduction_comp := X.dualReduction_comp
  closed := X.dualInclusion_closed
  faithfullyFlat := X.dualReduction_faithfullyFlat
  kernel := X.dual_kernel
  inclusion_reduction := X.dualInclusion_reduction
  reduction_inclusion := X.dualReduction_inclusion
  killed n := (X.level n).cartierDual_killed (p ^ n) (X.killed n)
  rank n := (X.level n).cartierDual_rank.trans (X.rank n)

/-- Dual system levels are the specified integral dual local models. -/
@[simp] theorem cartierDual_level (n : ℕ) : X.cartierDual.level n = (X.level n).cartierDual := rfl

/-- The dual system inclusion retains the original transposed reduction. -/
@[simp] theorem cartierDual_inclusion {m n : ℕ} (h : m ≤ n) :
    X.cartierDual.inclusion h = (X.reduction h).cartierDual := rfl

/-- The dual system reduction retains the original transposed inclusion. -/
@[simp] theorem cartierDual_reduction {m n : ℕ} (h : m ≤ n) :
    X.cartierDual.reduction h = (X.inclusion h).cartierDual := rfl

end ThreeAdicPlan.PDivisibleSystem
