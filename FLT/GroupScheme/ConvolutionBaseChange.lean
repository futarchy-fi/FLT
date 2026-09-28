/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.IntegralGroupLike
public import Mathlib.LinearAlgebra.Dual.Basis

/-!
# Scalar extension of finite convolution algebras

The convolution dual of a finite free coalgebra commutes with scalar extension.
This supplies the coordinate-algebra part of Cartier duality without constructing
a second Hopf structure.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open WithConv

namespace Coalgebra

variable {R K C : Type*} [CommRing R] [CommRing K] [Algebra R K]
  [AddCommGroup C] [Module R C] [Coalgebra R C]

/-- Extension of functionals as a map between convolution algebras. -/
def extendConvolution : WithConv (C →ₗ[R] R) →ₐ[R]
    WithConv (K ⊗[R] C →ₗ[K] K) where
  toFun f := toConv (extendFunctional f.ofConv)
  map_one' := WithConv.ext extendFunctional_one
  map_mul' f g := WithConv.ext (extendFunctional_convMul f g)
  map_zero' := by apply WithConv.ext; simp [extendFunctional]
  map_add' f g := by
    apply WithConv.ext
    simp [extendFunctional, LinearMap.baseChange_add, LinearMap.comp_add]
  commutes' r := by
    apply WithConv.ext
    ext c
    simp [extendFunctional_tmul, Algebra.smul_def, mul_comm]

/-- The scalar actions on the generic convolution algebra form the expected tower. -/
instance convolutionScalarTower :
    IsScalarTower R K (WithConv (K ⊗[R] C →ₗ[K] K)) where
  smul_assoc r k f := by
    apply WithConv.ext
    exact smul_assoc r k f.ofConv

/-- The natural scalar-extension map for convolution dual algebras. -/
def convolutionBaseChange : K ⊗[R] WithConv (C →ₗ[R] R) →ₐ[K]
    WithConv (K ⊗[R] C →ₗ[K] K) :=
  AlgHom.liftEquiv R K _ _ extendConvolution

/-- Evaluation of the scalar-extension map on a pure tensor. -/
@[simp] theorem convolutionBaseChange_tmul (k : K) (f : WithConv (C →ₗ[R] R)) :
    convolutionBaseChange (k ⊗ₜ[R] f) = k • toConv (extendFunctional f.ofConv) := rfl

set_option maxRecDepth 2000 in
/-- Finite freeness makes scalar extension of convolution duals bijective. -/
theorem convolutionBaseChange_bijective [Module.Free R C] [Module.Finite R C] :
    Function.Bijective (convolutionBaseChange (R := R) (K := K) (C := C)) := by
  classical
  let b := Module.Free.chooseBasis R C
  let d := b.dualBasis.map (WithConv.linearEquiv R (C →ₗ[R] R)).symm
  let e := (b.baseChange K).dualBasis.map
    (WithConv.linearEquiv K (K ⊗[R] C →ₗ[K] K)).symm
  let E := (d.baseChange K).equiv e (Equiv.refl _)
  have h : (convolutionBaseChange (R := R) (K := K) (C := C)).toLinearMap = E := by
    apply (d.baseChange K).ext
    intro i
    change convolutionBaseChange ((d.baseChange K) i) = E ((d.baseChange K) i)
    rw [show E ((d.baseChange K) i) = e i by
      simp only [E, Module.Basis.equiv_apply, Equiv.refl_apply]]
    simp only [Module.Basis.baseChange_apply, convolutionBaseChange_tmul, one_smul,
      d, e, Module.Basis.map_apply, WithConv.symm_linearEquiv_apply]
    apply WithConv.ext
    change extendFunctional (K := K) (b.dualBasis i) = (b.baseChange K).dualBasis i
    simpa only [Module.Basis.coe_dualBasis] using extendFunctional_coord b i
  change Function.Bijective (convolutionBaseChange (R := R) (K := K) (C := C)).toLinearMap
  rw [h]
  exact E.bijective

/-- The convolution dual of a finite free coalgebra commutes with scalar extension. -/
def convolutionBaseChangeEquiv [Module.Free R C] [Module.Finite R C] :
    K ⊗[R] WithConv (C →ₗ[R] R) ≃ₐ[K] WithConv (K ⊗[R] C →ₗ[K] K) :=
  AlgEquiv.ofBijective convolutionBaseChange convolutionBaseChange_bijective

/-- The scalar-extension equivalence is given by the natural map. -/
@[simp] theorem convolutionBaseChangeEquiv_apply [Module.Free R C] [Module.Finite R C]
    (t : K ⊗[R] WithConv (C →ₗ[R] R)) :
    convolutionBaseChangeEquiv t = convolutionBaseChange t := rfl

end Coalgebra

namespace CoalgHom

variable {R C D : Type*} [CommRing R]
  [AddCommGroup C] [Module R C] [Coalgebra R C]
  [AddCommGroup D] [Module R D] [Coalgebra R D]

/-- Precomposition with a coalgebra map is a morphism of convolution dual algebras. -/
def convolutionDual (f : C →ₗc[R] D) :
    WithConv (D →ₗ[R] R) →ₐ[R] WithConv (C →ₗ[R] R) where
  toFun g := toConv (g.ofConv.comp f.toLinearMap)
  map_one' := by apply WithConv.ext; ext c; simp
  map_mul' g h := WithConv.ext (LinearMap.convMul_comp_coalgHom_distrib g h f)
  map_zero' := by apply WithConv.ext; rfl
  map_add' g h := by apply WithConv.ext; rfl
  commutes' r := by apply WithConv.ext; ext c; simp

/-- The dual coalgebra map acts by precomposition on functionals. -/
@[simp] theorem convolutionDual_apply (f : C →ₗc[R] D)
    (g : WithConv (D →ₗ[R] R)) (c : C) : f.convolutionDual g c = g (f c) := rfl

end CoalgHom
