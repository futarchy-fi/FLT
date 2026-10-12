/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentSplitChart

/-!
# Both tangent orientations on the complete split smooth chart

The other coefficient branch keeps the same original chart functions and
sends the tangent ratio to the positive Laurent unit. The first branch
sends it to the inverse. Both comparisons are equalities of entire ring maps.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct LaurentPolynomial
namespace FLT.Mazur
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] (a : Rˣ)
local notation "W" => splitNodalEquation a
local notation "S" => AdjoinRoot (nodeTangentPolynomial W)
local notation "A" => Coordinate W 1
local notation "cx" => coord W 1 0
local notation "U" => splitTangentOpenRing a
/-- Use the chart comparison's fixed tensor ring structure. -/
local instance splitTangentLaurentTensorCommRing : CommRing (S ⊗[R] A) :=
  splitTangentTensorCommRing a
/-- Use the chart comparison's fixed localization ring structure. -/
local instance splitTangentLaurentOpenCommRing : CommRing U := splitTangentOpenCommRing a
local notation "σ" => nodeTangentTensorOpenConjugation W cx (1 : A)

/-- The second root is obtained by the actual coefficient conjugation. -/
def splitTangentOther : S →ₐ[R] R :=
  (splitTangentZero a).comp (nodeTangentConjugation W).toAlgHom

@[simp] theorem splitTangentOther_root :
    splitTangentOther a (AdjoinRoot.root (nodeTangentPolynomial W)) = -(a : R) := by
  change splitTangentZero a (nodeTangentConjugationHom W _) = _
  rw [nodeTangentConjugationHom_root, map_sub, map_neg, AlgHom.commutes,
    splitTangentZero_root, sub_zero]
  rfl

/-- The other coefficient branch of the same invariant tangent open. -/
def splitTangentOtherOpenChart : U →+* A := (splitTangentOpenChart a).comp σ

/-- Both branches keep the original smooth chart; only the chosen tangent root changes. -/
theorem splitTangentOtherOpenChart_original (b : A) :
    splitTangentOtherOpenChart a ((algebraMap (S ⊗[R] A) U) ((1 : S) ⊗ₜ[R] b)) = b := by
  simp [splitTangentOtherOpenChart, TensorCoefficientSymmetry.equiv_tmul]

/-- The second branch gives the positive, established Laurent parameter. -/
theorem splitTangentOtherOpenChart_parameter :
    Units.map (splitTangentOtherOpenChart a).toMonoidHom
        (nodeTangentTensorOpenParameter W cx (1 : A)) = splitNodalTangentUnit a := by
  change Units.map (splitTangentOpenChart a).toMonoidHom
    (Units.map (σ).toMonoidHom (nodeTangentTensorOpenParameter W cx (1 : A))) = _
  rw [nodeTangentTensorOpenParameter_conjugate, map_inv,
    splitTangentOpenChart_parameter, inv_inv]

/-- The first branch retains exactly the zero-root specialization of coefficients. -/
theorem splitTangentOpenChart_coeff (s : S) :
    splitTangentOpenChart a ((algebraMap S U) s) = algebraMap R A (splitTangentZero a s) := by
  rw [IsScalarTower.algebraMap_apply S (S ⊗[R] A) U,
    splitTangentOpenChart_algebraMap]
  change splitTangentChart a (s ⊗ₜ[R] (1 : A)) = _
  rw [splitTangentChart_tmul, mul_one]

/-- The second branch retains exactly the companion-root specialization of coefficients. -/
theorem splitTangentOtherOpenChart_coeff (s : S) :
    splitTangentOtherOpenChart a ((algebraMap S U) s) =
      algebraMap R A (splitTangentOther a s) := by
  rw [splitTangentOtherOpenChart, RingHom.comp_apply,
    nodeTangentTensorOpenConjugation_coeff, splitTangentOpenChart_coeff]
  rfl

/-- The full Laurent map on the first branch has inverse orientation. -/
theorem splitTangentOpenChart_laurent :
    (splitTangentOpenChart a).comp (nodeTangentTensorLaurentParameter W cx (1 : A)) =
      (splitNodalLaurentToChart a).toRingHom.comp (LaurentPolynomial.invert.toRingHom.comp
        (PolygonScalingNaturality.coeffMap (splitTangentZero a).toRingHom)) := by
  have ht := congrArg Units.val (splitTangentOpenChart_parameter a)
  have hi := congrArg (fun t : Aˣ => (t⁻¹ : Aˣ).val) (splitTangentOpenChart_parameter a)
  apply PolygonScalingNaturality.ringHom_ext
  · intro s
    simpa [nodeTangentTensorLaurentParameter, splitNodalLaurentToChart] using
      splitTangentOpenChart_coeff a s
  · simpa [nodeTangentTensorLaurentParameter, splitNodalLaurentToChart] using ht
  · simpa [nodeTangentTensorLaurentParameter, splitNodalLaurentToChart] using hi

/-- The full Laurent map on the other branch has the original positive orientation. -/
theorem splitTangentOtherOpenChart_laurent :
    (splitTangentOtherOpenChart a).comp
        (nodeTangentTensorLaurentParameter W cx (1 : A)) =
      (splitNodalLaurentToChart a).toRingHom.comp
        (PolygonScalingNaturality.coeffMap (splitTangentOther a).toRingHom) := by
  have ht := congrArg Units.val (splitTangentOtherOpenChart_parameter a)
  have hi := congrArg (fun t : Aˣ => (t⁻¹ : Aˣ).val)
    (splitTangentOtherOpenChart_parameter a)
  apply PolygonScalingNaturality.ringHom_ext
  · intro s
    simpa [nodeTangentTensorLaurentParameter, splitNodalLaurentToChart] using
      splitTangentOtherOpenChart_coeff a s
  · simpa [nodeTangentTensorLaurentParameter, splitNodalLaurentToChart] using ht
  · simpa [nodeTangentTensorLaurentParameter, splitNodalLaurentToChart] using hi

end FLT.Mazur
