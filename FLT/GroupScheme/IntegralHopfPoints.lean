/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.KummerPoints
public import FLT.GroupScheme.HopfPointCongruence
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Integral lifts of finite Hopf-algebra points

Restriction from the generic fibre and extension of the target preserve convolution.
Finite coordinate algebras have integral-valued points, so residue-kernel rigidity
can be applied in an integral closure.
-/

@[expose] public noncomputable section
open WithConv
open scoped TensorProduct
namespace ThreeAdicPlan

variable {R A B C : Type*} [CommRing R] [CommRing A] [Bialgebra R A]
  [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]

/-- Forgetting multiplication on the source preserves convolution of points. -/
def convolutionLinearMap : WithConv (A →ₐ[R] B) →* WithConv (A →ₗ[R] B) where
  toFun f := toConv f.ofConv.toLinearMap
  map_one' := rfl
  map_mul' := AlgHom.toLinearMap_convMul

/-- Postcomposition by an algebra homomorphism preserves convolution. -/
def convolutionPostcomp (j : B →ₐ[R] C) :
    WithConv (A →ₐ[R] B) →* WithConv (A →ₐ[R] C) where
  toFun f := toConv (j.comp f.ofConv)
  map_one' := by apply WithConv.ext; ext a; simp
  map_mul' f g := congrArg toConv (AlgHom.comp_convMul_distrib j f g)

/-- A faithful target embedding detects equality of convolution points. -/
theorem convolutionPostcomp_injective (j : B →ₐ[R] C) (hj : Function.Injective j) :
    Function.Injective (convolutionPostcomp (A := A) j) := by
  intro f g h
  apply WithConv.ext
  ext a
  exact hj (congrArg (fun t : WithConv (A →ₐ[R] C) ↦ t a) h)

/-- Restriction of generic-fibre points preserves convolution, including its unit. -/
def genericPointConvolution (R K L H : Type) [CommRing R] [Field K] [Field L]
    [CommRing H] [Algebra R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [Bialgebra R H] : (K ⊗[R] H →ₐ[K] L) →* WithConv (H →ₐ[R] L) where
  toFun f := toConv (Bialgebra.restrictPoints R K L H f)
  map_one' := by
    apply WithConv.ext
    ext a
    change algebraMap K L (Coalgebra.counit (R := K) ((1 : K) ⊗ₜ[R] a)) =
      algebraMap R L (Coalgebra.counit (R := R) a)
    simp [Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
  map_mul' f g := by
    apply WithConv.ext
    rw [Bialgebra.restrictPoints_mul]
    ext a
    exact (AlgHom.convMul_apply _ _ a).symm

/-- A point of a finite coordinate algebra takes integral values in every larger
coefficient ring in the tower. -/
def integralPointConvolution (O : Type*) [CommRing O] [Algebra R O]
    [Algebra O B] [IsScalarTower R O B] [Module.Finite R A] :
    WithConv (A →ₐ[R] B) →* WithConv (A →ₐ[R] integralClosure O B) where
  toFun f := toConv (f.ofConv.codRestrict ((integralClosure O B).restrictScalars R)
    (fun a ↦ ((Algebra.IsIntegral.isIntegral (R := R) a).map f.ofConv).tower_top))
  map_one' := by apply WithConv.ext; ext a; rfl
  map_mul' f g := by
    apply convolutionPostcomp_injective
      ((integralClosure O B).val.restrictScalars R) Subtype.val_injective
    change toConv (f * g).ofConv = _
    rw [map_mul]
    rfl

/-- The integral lift has the original point as its underlying field-valued map. -/
@[simp] theorem integralPointConvolution_apply (O : Type*) [CommRing O] [Algebra R O]
    [Algebra O B] [IsScalarTower R O B] [Module.Finite R A]
    (f : WithConv (A →ₐ[R] B)) (a : A) :
    ((integralPointConvolution O f a : integralClosure O B) : B) = f a := rfl

end ThreeAdicPlan
