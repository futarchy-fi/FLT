/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight

/-! # Effective descent of affine points along a faithfully flat cover

The overlap equality is descent data. Its construction or correction is a separate problem.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace Algebra
variable {R A B D : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra R D] [Algebra B D] [IsScalarTower R B D]
  [Module.FaithfullyFlat B D]

/-- An actual affine point with equal overlap pullbacks descends uniquely to the base. -/
theorem existsUnique_point_of_faithfullyFlat (z : A →ₐ[R] D)
    (hz : ∀ a, z a ⊗ₜ[B] (1 : D) = (1 : D) ⊗ₜ[B] z a) :
    ∃! y : A →ₐ[R] B, (IsScalarTower.toAlgHom R B D).comp y = z := by
  have hex (a : A) : ∃ b : B, algebraMap B D b = z a :=
    (IsEffective.of_faithfullyFlat B D (z a)).mp (sub_eq_zero.mpr (hz a))
  choose f hf using hex
  have hi : Function.Injective (algebraMap B D) := FaithfulSMul.algebraMap_injective B D
  let y : A →ₐ[R] B :=
    { toFun := f
      map_zero' := hi (by rw [hf, map_zero, map_zero])
      map_one' := hi (by rw [hf, map_one, map_one])
      map_add' := fun a b ↦ hi (by rw [hf, map_add, map_add, hf, hf])
      map_mul' := fun a b ↦ hi (by rw [hf, map_mul, map_mul, hf, hf])
      commutes' := fun r ↦ hi (by rw [hf, z.commutes, ← IsScalarTower.algebraMap_apply]) }
  refine ⟨y, ?_, ?_⟩
  · ext a
    exact hf a
  · intro y' hy'
    ext a
    exact hi ((AlgHom.congr_fun hy' a).trans (hf a).symm)

omit [Module.FaithfullyFlat B D] in
/-- A prescribed reduction can be verified after any injective comparison on the quotient. -/
theorem point_descent_reduction {C E : Type*} [CommRing C] [CommRing E]
    [Algebra R C] [Algebra R E] (q : B →ₐ[R] C) (t : D →ₐ[R] E)
    (j : C →ₐ[R] E) (hj : Function.Injective j)
    (hcomm : t.comp (IsScalarTower.toAlgHom R B D) = j.comp q)
    (y : A →ₐ[R] B) (z : A →ₐ[R] D) (x : A →ₐ[R] C)
    (hy : (IsScalarTower.toAlgHom R B D).comp y = z)
    (hz : t.comp z = j.comp x) : q.comp y = x := by
  ext a
  apply hj
  have hc := AlgHom.congr_fun hcomm (y a)
  have he := AlgHom.congr_fun hy a
  have hx := AlgHom.congr_fun hz a
  exact hc.symm.trans ((congrArg t he).trans hx)

end Algebra
