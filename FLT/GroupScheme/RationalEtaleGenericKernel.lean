/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalEtaleClosed
public import FLT.GroupScheme.RationalEtaleReductionFlat
public import FLT.GroupScheme.RationalEtaleRanks
public import FLT.GroupScheme.GenericPointSurjectivity
public import FLT.GroupScheme.FiniteGroupKernelCard
public import FLT.GroupScheme.ModelKernelComposition

/-! # Exactness of the original quotient transitions on generic points -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan.PDivisibleSystem
variable {p height : ℕ} [Fact p.Prime]
variable (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
  ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- Original quotient reductions are surjective on the specified geometric points. -/
theorem rationalEtaleReduction_points_surjective {m n : ℕ} (h : m ≤ n) :
    Function.Surjective (genericHom (X.rationalEtaleReduction h)) :=
  ModelHom.genericHom_surjective_of_injective _
    (X.rationalEtaleReduction_faithfullyFlat h).injective

/-- The original quotient transitions have zero composite on geometric points. -/
theorem rationalEtaleTransition_points_zero (m n : ℕ) (x : (X.rationalEtaleLevel m).Points) :
    genericHom (X.rationalEtaleReduction (Nat.le_add_left n m))
      (genericHom (X.rationalEtaleInclusion (Nat.le_add_right m n)) x) = 0 := by
  obtain ⟨a, rfl⟩ := (X.level m).rationalComponentGenericProjection_surjective x
  have hi := DFunLike.congr_fun
    (X.inclusion (Nat.le_add_right m n)).rationalComponentGenericMap_naturality a
  have hq := DFunLike.congr_fun
    (X.reduction (Nat.le_add_left n m)).rationalComponentGenericMap_naturality
    (genericHom (X.inclusion (Nat.le_add_right m n)) a)
  have hz := ModelHom.comp_eq_zero_of_augmentation_le
    (X.inclusion (Nat.le_add_right m n)) (X.reduction (Nat.le_add_left n m)) (X.kernel m n).le
  have hp := congrArg (fun f ↦ genericHom f a) hz
  simp only [genericHom_comp, ModelHom.genericHom_zero] at hp
  simp only [DistribMulActionHom.comp_apply] at hi hq
  have he : (X.reduction (Nat.le_add_left n m)).rationalComponentGenericMap
      ((X.inclusion (Nat.le_add_right m n)).rationalComponentGenericMap
        ((X.level m).rationalComponentGenericProjection a)) = 0 := by
    rw [← hi, ← hq, hp, map_zero]
  change (genericHom (X.reduction (Nat.le_add_left n m)).rationalComponentMap)
    ((genericHom (X.inclusion (Nat.le_add_right m n)).rationalComponentMap) _) = 0
  simp only [ModelHom.rationalComponentMap_genericHom]
  convert he using 1

/-- The integral ranks and actual maps prove exactness of the quotient generic sequence. -/
theorem rationalEtaleTransition_points_exact (m n : ℕ)
    (x : (X.rationalEtaleLevel (m + n)).Points) :
    genericHom (X.rationalEtaleReduction (Nat.le_add_left n m)) x = 0 ↔
      ∃ a, genericHom (X.rationalEtaleInclusion (Nat.le_add_right m n)) a = x := by
  apply AddMonoidHom.exact_of_card_mul
    (genericHom (X.rationalEtaleInclusion (Nat.le_add_right m n))).toAddMonoidHom
    (genericHom (X.rationalEtaleReduction (Nat.le_add_left n m))).toAddMonoidHom
    ((X.inclusion _).rationalComponentMap_generic_injective (X.closed _))
    (X.rationalEtaleReduction_points_surjective _) (X.rationalEtaleTransition_points_zero m n)
  rw [← FF.coordinate_finrank, ← FF.coordinate_finrank, ← FF.coordinate_finrank,
    X.rationalEtale_rank, X.rationalEtale_rank, X.rationalEtale_rank, Nat.add_mul, pow_add]
end ThreeAdicPlan.PDivisibleSystem
