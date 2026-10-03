/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonScalingNaturality
public import Mathlib.RingTheory.TensorProduct.Maps
/-!
# Laurent polynomials commute with scalar extension

The two maps are tensor-product multiplication and Laurent evaluation at
the tensor coordinate unit. Constants and the inverse generators prove
that they are inverse, with explicit formulas on both tensor factors.
-/

open scoped LaurentPolynomial TensorProduct
@[expose] public noncomputable section
namespace FLT.Mazur.LaurentTensor
open PolygonScalingNaturality PolygonChartScaling
variable (K L : Type*) [CommRing K] [CommRing L] [Algebra K L]

/-- Extend Laurent coefficients while fixing its coordinate. -/
def coeff : K[T;T⁻¹] →ₐ[K] L[T;T⁻¹] where
  __ := coeffMap (algebraMap K L)
  commutes' r := by simp

/-- Multiply the coefficient factors in the Laurent tensor product. -/
def forward : L ⊗[K] K[T;T⁻¹] →ₐ[K] L[T;T⁻¹] :=
  Algebra.TensorProduct.lift (IsScalarTower.toAlgHom K L L[T;T⁻¹]) (coeff K L)
    (fun _ _ ↦ Commute.all _ _)

/-- Evaluate at the tensor coordinate unit to reverse coefficient extension. -/
def backward : L[T;T⁻¹] →ₐ[K] L ⊗[K] K[T;T⁻¹] where
  __ := LaurentPolynomial.eval₂
    (Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K[T;T⁻¹]).toRingHom
    (Units.map
      (Algebra.TensorProduct.includeRight : K[T;T⁻¹] →ₐ[K] L ⊗[K] K[T;T⁻¹]).toMonoidHom
      (coordinateUnit (1 : Kˣ)))
  commutes' r := by simp

theorem forward_backward : (forward K L).comp (backward K L) = AlgHom.id K _ := by
  apply AlgHom.coe_ringHom_injective
  apply ringHom_ext
  · intro r
    simp [backward, forward]
  · simp [backward, forward, coeff, coordinateUnit]
  · simp [backward, forward, coeff, coordinateUnit]

theorem backward_forward : (backward K L).comp (forward K L) = AlgHom.id K _ := by
  apply Algebra.TensorProduct.ext
  · ext r
    simp [forward, backward, Algebra.TensorProduct.includeLeft_apply]
  · apply AlgHom.coe_ringHom_injective
    apply ringHom_ext
    · intro a
      simpa [forward, backward, coeff] using
        (Algebra.TensorProduct.includeRight : K[T;T⁻¹] →ₐ[K] L ⊗[K] K[T;T⁻¹]).commutes a |>.symm
    · simp [forward, backward, coeff, coordinateUnit]
    · simp [forward, backward, coeff, coordinateUnit]

/-- Laurent polynomials commute with scalar extension. -/
def equivalence : L ⊗[K] K[T;T⁻¹] ≃ₐ[K] L[T;T⁻¹] :=
  AlgEquiv.ofAlgHom (forward K L) (backward K L) (forward_backward K L) (backward_forward K L)

@[simp] theorem equivalence_left (a : L) :
    equivalence K L (a ⊗ₜ[K] 1) = LaurentPolynomial.C a := by
  simp [equivalence, forward]

@[simp] theorem equivalence_right (p : K[T;T⁻¹]) :
    equivalence K L (1 ⊗ₜ[K] p) = coeffMap (algebraMap K L) p := by
  simp [equivalence, forward, coeff]
end FLT.Mazur.LaurentTensor
