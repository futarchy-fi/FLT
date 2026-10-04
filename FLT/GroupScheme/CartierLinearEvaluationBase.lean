/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CartierLinearEvaluation

/-! # Linear Cartier evaluation over the original base ring -/

@[expose] public noncomputable section
namespace HopfAlgebra.CartierDual
variable {R A : Type} [CommRing R] [CommRing A]
  [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A]

/-- Over the base ring, linear Cartier evaluation is evaluation on the dual functional. -/
theorem linearTestEvaluation_base (χ : CartierDual R A →ₗ[R] R) (f : A →ₗ[R] R) :
    linearTestEvaluation χ f = χ (WithConv.toConv f) := by
  let b := Module.Free.chooseBasis R A
  rw [linearTestEvaluation_eq_sum b]
  have hf : WithConv.toConv f = ∑ i, f (b i) • WithConv.toConv (b.coord i) := by
    apply WithConv.ext
    ext a
    simp only [WithConv.ofConv_sum, WithConv.ofConv_smul]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    simpa only [map_sum, map_smul, smul_eq_mul, mul_comm, Module.Basis.coord_apply] using
      congrArg f (b.sum_repr a).symm
  rw [hf, map_sum]
  simp

end HopfAlgebra.CartierDual
