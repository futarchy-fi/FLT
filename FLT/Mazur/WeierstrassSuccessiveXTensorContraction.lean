/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXBaseChangeCoordinates
public import FLT.Mazur.WeierstrassSuccessiveXContraction

/-!
# The original contraction inside the actual successive tensor fiber

The original preceding-chart map is included into the tensor fiber. Its
horizontal function is the retained u and its vertical function is u*v.
The whole map, not just those two values, agrees with coefficient extension.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (S : Type*) [CommRing S] [Algebra R S]

/-- Include actual successive-chart functions into their scalar extension. -/
def tensorInclusion : Coordinate W s π b3 b4 b6 →ₐ[R]
    ScalarExtension W s π b3 b4 b6 S := Algebra.TensorProduct.includeRight

/-- The tensor inclusion sends each original generator to its named pure tensor. -/
@[simp] theorem tensorInclusion_coord (i : Fin 3) :
    tensorInclusion W s π b3 b4 b6 S (coord W s π b3 b4 b6 i) =
      tensorCoord W s π b3 b4 b6 S i := rfl

/-- The full coefficient comparison preserves the actual original inclusion. -/
theorem baseChangeEquiv_inclusion :
    ((baseChangeEquiv W s π b3 b4 b6 S).toAlgHom.restrictScalars R).comp
        (tensorInclusion W s π b3 b4 b6 S) = coefficientMap W s π b3 b4 b6 S := by
  apply hom_ext
  intro i
  simp

/-- The actual preceding contraction followed by passage to the tensor fiber. -/
def tensorPreviousMap :
    WeierstrassDilatation.Coordinate W s (π * b3) (π * b4) (π ^ 2 * b6) →ₐ[R]
      ScalarExtension W s π b3 b4 b6 S :=
  (tensorInclusion W s π b3 b4 b6 S).comp (fromDivided W s π b3 b4 b6)

/-- The original preceding horizontal coordinate is exactly the retained tensor u. -/
@[simp] theorem tensorPreviousMap_x : tensorPreviousMap W s π b3 b4 b6 S
    (WeierstrassDilatation.x W s (π * b3) (π * b4) (π ^ 2 * b6)) =
      tensorCoord W s π b3 b4 b6 S 2 := by
  simp only [tensorPreviousMap, AlgHom.comp_apply, fromDivided_x, tensorInclusion_coord]

/-- The original preceding vertical coordinate is exactly the tensor product u*v. -/
@[simp] theorem tensorPreviousMap_y : tensorPreviousMap W s π b3 b4 b6 S
    (WeierstrassDilatation.y W s (π * b3) (π * b4) (π ^ 2 * b6)) =
      tensorCoord W s π b3 b4 b6 S 2 * tensorCoord W s π b3 b4 b6 S 1 := by
  simp only [tensorPreviousMap, AlgHom.comp_apply, fromDivided_y, map_mul,
    tensorInclusion_coord]

/-- The coefficient comparison preserves the entire original contraction. -/
theorem baseChangeEquiv_previousMap :
    ((baseChangeEquiv W s π b3 b4 b6 S).toAlgHom.restrictScalars R).comp
        (tensorPreviousMap W s π b3 b4 b6 S) =
      (coefficientMap W s π b3 b4 b6 S).comp (fromDivided W s π b3 b4 b6) := by
  rw [tensorPreviousMap, ← AlgHom.comp_assoc, baseChangeEquiv_inclusion]

end FLT.Mazur.WeierstrassSuccessiveX
