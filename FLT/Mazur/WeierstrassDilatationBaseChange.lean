/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationCoefficients
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Actual coefficient base change of the divided nodal chart

The tensor product is explicitly isomorphic to the divided chart of the
coefficient-extended equation. Both maps are proved inverse on the original
universal coordinates; no flatness of the coefficient extension is required.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.WeierstrassDilatation

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (S : Type*) [CommRing S] [Algebra R S]

/-- A named tensor algebra prevents expansion of its operations in chart proofs. -/
def ScalarExtension := S ⊗[R] Coordinate W s b3 b4 b6

instance scalarExtensionCommRing : CommRing (ScalarExtension W s b3 b4 b6 S) :=
  inferInstanceAs (CommRing (S ⊗[R] Coordinate W s b3 b4 b6))

instance scalarExtensionAlgebra : Algebra R (ScalarExtension W s b3 b4 b6 S) :=
  inferInstanceAs (Algebra R (S ⊗[R] Coordinate W s b3 b4 b6))

instance scalarExtensionAlgebraBase : Algebra S (ScalarExtension W s b3 b4 b6 S) :=
  inferInstanceAs (Algebra S (S ⊗[R] Coordinate W s b3 b4 b6))

instance scalarExtensionTower : IsScalarTower R S (ScalarExtension W s b3 b4 b6 S) :=
  inferInstanceAs (IsScalarTower R S (S ⊗[R] Coordinate W s b3 b4 b6))

/-- The coefficient map induces the map from the actual tensor product. -/
def baseChangeForward : ScalarExtension W s b3 b4 b6 S →ₐ[S]
    ExtendedCoordinate W s b3 b4 b6 S :=
  AlgHom.liftEquiv R S _ _ (coefficientMap W s b3 b4 b6 S)

/-- On pure tensors, coefficient extension is multiplication by the new scalar. -/
@[simp] theorem baseChangeForward_tmul (a : S) (z : Coordinate W s b3 b4 b6) :
    baseChangeForward W s b3 b4 b6 S (a ⊗ₜ[R] z) =
      a • coefficientMap W s b3 b4 b6 S z := rfl

/-- The old universal coordinates solve the extended equation in the tensor algebra. -/
theorem baseChange_equation :
    let T := ScalarExtension W s b3 b4 b6 S
    let u : T := (1 : S) ⊗ₜ[R] x W s b3 b4 b6
    let v : T := (1 : S) ⊗ₜ[R] y W s b3 b4 b6
    v ^ 2 + (algebraMap S T ((W.map (algebraMap R S)).a₁) * u +
        algebraMap S T (algebraMap R S b3)) * v =
      algebraMap S T (algebraMap R S s) * u ^ 3 +
        algebraMap S T ((W.map (algebraMap R S)).a₂) * u ^ 2 +
        algebraMap S T (algebraMap R S b4) * u +
        algebraMap S T (algebraMap R S b6) := by
  let f : Coordinate W s b3 b4 b6 →ₐ[R] ScalarExtension W s b3 b4 b6 S :=
    Algebra.TensorProduct.includeRight
  have hf (z : Coordinate W s b3 b4 b6) : f z = (1 : S) ⊗ₜ[R] z := rfl
  simpa only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    ← IsScalarTower.algebraMap_apply R S, hf] using
    equation_map (S := ScalarExtension W s b3 b4 b6 S) W s b3 b4 b6 f

/-- Evaluation in the tensor product supplies the inverse on the specialized chart. -/
def baseChangeBackward : ExtendedCoordinate W s b3 b4 b6 S →ₐ[S]
    ScalarExtension W s b3 b4 b6 S :=
  evaluation (W.map (algebraMap R S))
    (algebraMap R S s) (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6)
    ((1 : S) ⊗ₜ[R] x W s b3 b4 b6) ((1 : S) ⊗ₜ[R] y W s b3 b4 b6)
    (baseChange_equation W s b3 b4 b6 S)

/-- The inverse sends the first coordinate to its original pure tensor. -/
@[simp] theorem baseChangeBackward_x :
    baseChangeBackward W s b3 b4 b6 S
      (x (W.map (algebraMap R S))
        (algebraMap R S s) (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6)) =
      (1 : S) ⊗ₜ[R] x W s b3 b4 b6 := evaluation_x _ _ _ _ _ _ _ _

/-- The inverse sends the second coordinate to its original pure tensor. -/
@[simp] theorem baseChangeBackward_y :
    baseChangeBackward W s b3 b4 b6 S
      (y (W.map (algebraMap R S))
        (algebraMap R S s) (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6)) =
      (1 : S) ⊗ₜ[R] y W s b3 b4 b6 := evaluation_y _ _ _ _ _ _ _ _

/-- The two maps fix the specialized chart. -/
theorem baseChangeForward_backward :
    (baseChangeForward W s b3 b4 b6 S).comp (baseChangeBackward W s b3 b4 b6 S) =
      AlgHom.id S _ := by
  apply hom_ext <;>
    simp only [AlgHom.comp_apply, baseChangeBackward_x, baseChangeBackward_y,
      baseChangeForward_tmul, one_smul, coefficientMap_x, coefficientMap_y, AlgHom.id_apply]

/-- They also fix the actual tensor product over the original coefficient ring. -/
theorem baseChangeBackward_forward :
    (baseChangeBackward W s b3 b4 b6 S).comp (baseChangeForward W s b3 b4 b6 S) =
      AlgHom.id S _ := by
  apply Algebra.TensorProduct.ext_ring
  apply hom_ext
  · change baseChangeBackward W s b3 b4 b6 S
      (baseChangeForward W s b3 b4 b6 S ((1 : S) ⊗ₜ[R] x W s b3 b4 b6)) = _
    rw [baseChangeForward_tmul, one_smul, coefficientMap_x, baseChangeBackward_x]
    rfl
  · change baseChangeBackward W s b3 b4 b6 S
      (baseChangeForward W s b3 b4 b6 S ((1 : S) ⊗ₜ[R] y W s b3 b4 b6)) = _
    rw [baseChangeForward_tmul, one_smul, coefficientMap_y, baseChangeBackward_y]
    rfl

/-- Arbitrary coefficient extension recovers the actual specialized divided chart. -/
def baseChangeEquiv : ScalarExtension W s b3 b4 b6 S ≃ₐ[S]
    ExtendedCoordinate W s b3 b4 b6 S :=
  AlgEquiv.ofAlgHom (baseChangeForward W s b3 b4 b6 S) (baseChangeBackward W s b3 b4 b6 S)
    (baseChangeForward_backward W s b3 b4 b6 S) (baseChangeBackward_forward W s b3 b4 b6 S)

end FLT.Mazur.WeierstrassDilatation
