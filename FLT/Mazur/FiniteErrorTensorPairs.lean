/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteErrorKernelPairs
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Constructing ambient tensor solutions from finite errors

The multiplier is a scalar in the ambient algebra. Corrections lie in the
tensor of the entire original chart family, without any finite index assumption.
No flatness is needed to construct the ambient solution; flatness is used only
later to descend that solution to the original scalar ring.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.FiniteErrorLinearLifting
variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (S : Type*) [CommRing S] [Algebra R S]

/-- Assemble an ambient scalar and one shared tensor correction family. -/
def tensorPair : (S × S ⊗[R] M) →ₗ[S] S ⊗[R] (R × M) :=
  LinearMap.coprod (LinearMap.toSpanSingleton S _ (1 ⊗ₜ[R] (1, 0)))
    ((LinearMap.inr R R M).baseChange S)

/-- The assembled pair contains exactly the given scalar and chart family. -/
theorem tensorPair_apply (a : S) (z : S ⊗[R] M) :
    tensorPair (R := R) S (a, z) =
      a ⊗ₜ[R] (1, 0) + (LinearMap.inr R R M).baseChange S z := by
  simp [tensorPair, smul_tmul']

/-- The first tensor coordinate of the assembled pair is its prescribed multiplier. -/
theorem tensorPair_fst (a : S) (z : S ⊗[R] M) :
    (LinearMap.fst R R M).baseChange S (tensorPair S (a, z)) = a ⊗ₜ[R] 1 := by
  rw [tensorPair_apply, map_add, LinearMap.baseChange_tmul]
  have he : (LinearMap.fst R R M).baseChange S
      ((LinearMap.inr R R M).baseChange S z) = 0 := by
    change (((LinearMap.fst R R M).baseChange S).comp
      ((LinearMap.inr R R M).baseChange S)) z = 0
    rw [← LinearMap.baseChange_comp]
    have hzero : (LinearMap.fst R R M).comp (LinearMap.inr R R M) = 0 := by
      ext x
      rfl
    rw [hzero, LinearMap.baseChange_zero, LinearMap.zero_apply]
  rw [he, add_zero]
  rfl

variable [IsNoetherianRing S] (D : (R × M) →ₗ[R] N)
  (I : Ideal S) (E : Submodule S (S ⊗[R] N)) (hE : E.FG)

include hE in
/-- Uniformly finite errors construct an exact ambient solution with multiplier near one. -/
theorem exists_tensor_pair
    (h : ∀ n : ℕ, ∃ z : S ⊗[R] M,
      D.baseChange S (tensorPair S (1, z)) ∈ I ^ n • E) :
    ∃ (a : S) (z : S ⊗[R] M), a - 1 ∈ I ∧
      D.baseChange S (tensorPair S (a, z)) = 0 :=
  exists_kernel_pair ((D.baseChange S).comp (tensorPair S)) I E hE h

include hE in
/-- The constructed ambient solution avoids each proper ideal containing the error ideal. -/
theorem exists_tensor_pair_nonvanishing
    (h : ∀ n : ℕ, ∃ z : S ⊗[R] M,
      D.baseChange S (tensorPair S (1, z)) ∈ I ^ n • E)
    (P : Ideal S) (hIP : I ≤ P) (hP : P ≠ ⊤) :
    ∃ (a : S) (z : S ⊗[R] M), a ∉ P ∧
      D.baseChange S (tensorPair S (a, z)) = 0 :=
  exists_kernel_pair_nonvanishing ((D.baseChange S).comp (tensorPair S)) I E hE h P hIP hP

end FLT.Mazur.FiniteErrorLinearLifting
