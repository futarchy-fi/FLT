/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXCoefficients
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# The actual tensor fiber of a successive three-coordinate chart

Arbitrary scalar extension is isomorphic to the coefficient-extended
three-generator equation. Both inverse maps retain t, v, and u; the
horizontal coordinate is never eliminated at a bad fiber.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (S : Type*) [CommRing S] [Algebra R S]

/-- A named tensor algebra keeps its operations sealed during coordinate proofs. -/
def ScalarExtension := S ⊗[R] Coordinate W s π b3 b4 b6

instance scalarExtensionCommRing : CommRing (ScalarExtension W s π b3 b4 b6 S) :=
  inferInstanceAs (CommRing (S ⊗[R] Coordinate W s π b3 b4 b6))

instance scalarExtensionAlgebra : Algebra R (ScalarExtension W s π b3 b4 b6 S) :=
  inferInstanceAs (Algebra R (S ⊗[R] Coordinate W s π b3 b4 b6))

instance scalarExtensionAlgebraBase : Algebra S (ScalarExtension W s π b3 b4 b6 S) :=
  inferInstanceAs (Algebra S (S ⊗[R] Coordinate W s π b3 b4 b6))

instance scalarExtensionTower : IsScalarTower R S (ScalarExtension W s π b3 b4 b6 S) :=
  inferInstanceAs (IsScalarTower R S (S ⊗[R] Coordinate W s π b3 b4 b6))

/-- The original three generators in the actual tensor product. -/
def tensorCoord (i : Fin 3) : ScalarExtension W s π b3 b4 b6 S :=
  (1 : S) ⊗ₜ[R] coord W s π b3 b4 b6 i

/-- Extend the actual coefficient map to the tensor product. -/
def baseChangeForward : ScalarExtension W s π b3 b4 b6 S →ₐ[S]
    ExtendedCoordinate W s π b3 b4 b6 S :=
  AlgHom.liftEquiv R S _ _ (coefficientMap W s π b3 b4 b6 S)

/-- The tensor map retains each original generator. -/
@[simp] theorem baseChangeForward_coord (i : Fin 3) :
    baseChangeForward W s π b3 b4 b6 S (tensorCoord W s π b3 b4 b6 S i) =
      extendedCoord W s π b3 b4 b6 S i := by
  change (1 : S) • coefficientMap W s π b3 b4 b6 S (coord W s π b3 b4 b6 i) = _
  rw [one_smul, coefficientMap_coord]

/-- The old coordinates satisfy the extended divided equation in the tensor algebra. -/
theorem baseChange_equation :
    let T := ScalarExtension W s π b3 b4 b6 S
    let c := tensorCoord W s π b3 b4 b6 S
    c 1 ^ 2 + (algebraMap S T (W.map (algebraMap R S)).a₁ +
      algebraMap S T (algebraMap R S b3) * c 0) * c 1 =
        algebraMap S T (algebraMap R S s) * c 2 +
          algebraMap S T (W.map (algebraMap R S)).a₂ +
          algebraMap S T (algebraMap R S b4) * c 0 +
          algebraMap S T (algebraMap R S b6) * c 0 ^ 2 := by
  let f : Coordinate W s π b3 b4 b6 →ₐ[R] ScalarExtension W s π b3 b4 b6 S :=
    Algebra.TensorProduct.includeRight
  have hf (i : Fin 3) : f (coord W s π b3 b4 b6 i) =
      tensorCoord W s π b3 b4 b6 S i := rfl
  simpa only [hf, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    ← IsScalarTower.algebraMap_apply R S] using equation_map W s π b3 b4 b6 f

/-- The original incidence equation also survives in the tensor algebra. -/
theorem baseChange_incidence :
    tensorCoord W s π b3 b4 b6 S 0 * tensorCoord W s π b3 b4 b6 S 2 =
      algebraMap S (ScalarExtension W s π b3 b4 b6 S) (algebraMap R S π) := by
  let f : Coordinate W s π b3 b4 b6 →ₐ[R] ScalarExtension W s π b3 b4 b6 S :=
    Algebra.TensorProduct.includeRight
  have hf (i : Fin 3) : f (coord W s π b3 b4 b6 i) =
      tensorCoord W s π b3 b4 b6 S i := rfl
  simpa only [hf, ← IsScalarTower.algebraMap_apply R S] using incidence_map W s π b3 b4 b6 f

/-- Evaluate the extended equation in its actual tensor product. -/
def baseChangeBackward : ExtendedCoordinate W s π b3 b4 b6 S →ₐ[S]
    ScalarExtension W s π b3 b4 b6 S :=
  evaluation (W.map (algebraMap R S)) (algebraMap R S s) (algebraMap R S π)
    (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6)
    (tensorCoord W s π b3 b4 b6 S)
    (baseChange_equation W s π b3 b4 b6 S) (baseChange_incidence W s π b3 b4 b6 S)

/-- The inverse retains all three tensor coordinates. -/
@[simp] theorem baseChangeBackward_coord (i : Fin 3) :
    baseChangeBackward W s π b3 b4 b6 S (extendedCoord W s π b3 b4 b6 S i) =
      tensorCoord W s π b3 b4 b6 S i := evaluation_coord _ _ _ _ _ _ _ _ _ i

/-- The coefficient equation is recovered by the two actual maps. -/
theorem baseChangeForward_backward :
    (baseChangeForward W s π b3 b4 b6 S).comp (baseChangeBackward W s π b3 b4 b6 S) =
      AlgHom.id S _ := by
  apply hom_ext
  intro i
  change baseChangeForward W s π b3 b4 b6 S
    (baseChangeBackward W s π b3 b4 b6 S (extendedCoord W s π b3 b4 b6 S i)) = _
  rw [baseChangeBackward_coord, baseChangeForward_coord]
  rfl

/-- The original tensor algebra is recovered by the two actual maps. -/
theorem baseChangeBackward_forward :
    (baseChangeBackward W s π b3 b4 b6 S).comp (baseChangeForward W s π b3 b4 b6 S) =
      AlgHom.id S _ := by
  apply Algebra.TensorProduct.ext_ring
  apply hom_ext
  intro i
  change baseChangeBackward W s π b3 b4 b6 S
    (baseChangeForward W s π b3 b4 b6 S (tensorCoord W s π b3 b4 b6 S i)) = _
  rw [baseChangeForward_coord, baseChangeBackward_coord]
  rfl

/-- Arbitrary base change preserves the actual full three-coordinate equation chart. -/
def baseChangeEquiv : ScalarExtension W s π b3 b4 b6 S ≃ₐ[S]
    ExtendedCoordinate W s π b3 b4 b6 S :=
  AlgEquiv.ofAlgHom (baseChangeForward W s π b3 b4 b6 S) (baseChangeBackward W s π b3 b4 b6 S)
    (baseChangeForward_backward W s π b3 b4 b6 S) (baseChangeBackward_forward W s π b3 b4 b6 S)

end FLT.Mazur.WeierstrassSuccessiveX
