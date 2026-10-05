/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlaceComplexCoefficients
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Scalar extension from the original rational-place integral base to C_p -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open PadicHodgeTheory
open scoped TensorProduct
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
attribute [local instance 2000] Algebra.toModule Algebra.toSMul
namespace ThreeAdicPlan
variable {p : ℕ} [Fact p.Prime]
local notation "O" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (LocalCyclotomic.rationalPlace p)

/-- The standard integral p-adic scalar action on C_p. -/
instance rationalPlaceComplexPadicIntAlgebra : Algebra ℤ_[p] ℂ_[p] :=
  ((algebraMap ℚ_[p] ℂ_[p]).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra

/-- The integral scalar action factors through Q_p. -/
instance rationalPlaceComplexPadicIntTower : IsScalarTower ℤ_[p] ℚ_[p] ℂ_[p] :=
  IsScalarTower.of_algebraMap_eq' (R := ℤ_[p]) (S := ℚ_[p]) (A := ℂ_[p]) rfl

/-- The inverse integral identification gives the usual scalar in C_p. -/
theorem rationalPlaceComplexAlgebra_symm (a : ℤ_[p]) :
    algebraMap O ℂ_[p] ((rationalPlaceIntegersEquiv p).symm a) =
      algebraMap ℤ_[p] ℂ_[p] a := by
  change algebraMap ℚ_[p] ℂ_[p]
    (rationalPlaceIntegersEquiv p ((rationalPlaceIntegersEquiv p).symm a)) = _
  rw [(rationalPlaceIntegersEquiv p).apply_symm_apply]
  rfl

variable {M N : Type*} [AddCommGroup M] [Module ℤ_[p] M]
  [AddCommGroup N]
  [Module ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ) N]

/-- Swap the coefficient factor and recover genuine Z_p-linearity from the original base map. -/
def rationalPlaceComplexLatticeMap
    (f : M →ₛₗ[(rationalPlaceIntegersEquiv p).symm.toRingHom] N ⊗[O] ℂ_[p]) :
    M →ₗ[ℤ_[p]] ℂ_[p] ⊗[O] N where
  toFun x := TensorProduct.comm O N ℂ_[p] (f x)
  map_add' x y := by simp only [map_add]
  map_smul' a x := by
    rw [f.map_smulₛₗ, map_smul]
    induction (TensorProduct.comm O N ℂ_[p]) (f x) using TensorProduct.inductionOn with
    | tmul c n =>
      simp only [TensorProduct.smul_tmul', Algebra.smul_def]
      change (algebraMap O ℂ_[p] ((rationalPlaceIntegersEquiv p).symm a) * c) ⊗ₜ n =
        (algebraMap ℤ_[p] ℂ_[p] a * c) ⊗ₜ n
      rw [rationalPlaceComplexAlgebra_symm]
    | add v w hv hw => simp only [smul_add, hv, hw]

/-- Extend an original lattice differential to a C_p-linear map on the whole Tate tensor. -/
def rationalPlaceComplexExtend
    (f : M →ₛₗ[(rationalPlaceIntegersEquiv p).symm.toRingHom] N ⊗[O] ℂ_[p]) :
    ℂ_[p] ⊗[ℤ_[p]] M →ₗ[ℂ_[p]] ℂ_[p] ⊗[O] N :=
  TensorProduct.AlgebraTensorModule.lift
    ((LinearMap.id : ℂ_[p] →ₗ[ℂ_[p]] ℂ_[p]).smulRight (rationalPlaceComplexLatticeMap f))

/-- The extension retains the specified lattice value on every pure tensor. -/
theorem rationalPlaceComplexExtend_tmul
    (f : M →ₛₗ[(rationalPlaceIntegersEquiv p).symm.toRingHom] N ⊗[O] ℂ_[p])
    (c : ℂ_[p]) (x : M) :
    rationalPlaceComplexExtend f (c ⊗ₜ x) =
      c • TensorProduct.comm O N ℂ_[p] (f x) := rfl

/-- A C_p-linear map is determined by its values on the original lattice. -/
theorem rationalPlaceComplexExtend_unique
    (f : M →ₛₗ[(rationalPlaceIntegersEquiv p).symm.toRingHom] N ⊗[O] ℂ_[p])
    (g : ℂ_[p] ⊗[ℤ_[p]] M →ₗ[ℂ_[p]] ℂ_[p] ⊗[O] N)
    (h : ∀ x, g (1 ⊗ₜ x) = TensorProduct.comm O N ℂ_[p] (f x)) :
    g = rationalPlaceComplexExtend f := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro c x
  rw [show c ⊗ₜ[ℤ_[p]] x = c • (1 ⊗ₜ[ℤ_[p]] x) by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul, h]
  rw [map_smul, rationalPlaceComplexExtend_tmul, one_smul]
end ThreeAdicPlan
