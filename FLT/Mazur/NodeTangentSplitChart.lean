/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentTensorLaurentDescent
public import FLT.Mazur.WeierstrassSplitNodalLaurent

/-!
# The original tangent open on a split nodal infinity chart

Evaluate the adjoined root at the first, zero tangent. The invariant open
maps to the entire original smooth chart; its tangent ratio is the inverse
of that chart's existing Laurent coordinate.
-/

@[expose] public noncomputable section
open scoped TensorProduct LaurentPolynomial
namespace FLT.Mazur
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (a : Rˣ)
local notation "W" => splitNodalEquation a
local notation "S" => AdjoinRoot (nodeTangentPolynomial W)
local notation "A" => Coordinate W 1
local notation "cx" => coord W 1 0
/-- The invariant open formed from the original split infinity chart coordinates. -/
abbrev splitTangentOpenRing := nodeTangentTensorOpen W cx (1 : A)
local notation "U" => splitTangentOpenRing a
/-- Fix the tensor ring instance before forming localization maps. -/
local instance splitTangentTensorCommRing : CommRing (S ⊗[R] A) := inferInstance
/-- Fix the localization ring instance used by the chart comparison. -/
local instance splitTangentOpenCommRing : CommRing U := inferInstance

/-- The actual zero-root point of the split tangent coefficient cover. -/
def splitTangentZero : S →ₐ[R] R :=
  AdjoinRoot.liftAlgHom _ (AlgHom.id R R) 0 (by simp [splitNodalEquation])

@[simp] theorem splitTangentZero_root :
    splitTangentZero a (AdjoinRoot.root (nodeTangentPolynomial W)) = 0 :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- Specialize only the adjoined coefficient, keeping every original chart function. -/
def splitTangentChart : S ⊗[R] A →ₐ[R] A :=
  Algebra.TensorProduct.lift ((Algebra.ofId R A).comp (splitTangentZero a))
    (AlgHom.id R A) (fun _ _ => Commute.all _ _)

@[simp] theorem splitTangentChart_tmul (s : S) (b : A) :
    splitTangentChart a (s ⊗ₜ[R] b) = algebraMap R A (splitTangentZero a s) * b := rfl

/-- The first original tangent factor is exactly one on the normalized Y chart. -/
@[simp] theorem splitTangentChart_first :
    splitTangentChart a (nodeTangentTensorFirst W cx (1 : A)) = 1 := by
  simp [nodeTangentTensorFirst]

/-- The other factor is the chart's existing unit, with its established orientation. -/
@[simp] theorem splitTangentChart_second :
    splitTangentChart a (nodeTangentTensorSecond W cx (1 : A)) =
      (splitNodalTangentUnit a : A) := by
  simp only [nodeTangentTensorSecond, map_add, splitTangentChart_tmul, map_one,
    one_mul, AlgHom.commutes, splitTangentZero_root, add_zero]
  rfl

/-- The whole Y chart lies in the invariant tangent open. -/
def splitTangentOpenChart : U →+* A :=
  IsLocalization.Away.lift
    (nodeTangentTensorFirst W cx (1 : A) * nodeTangentTensorSecond W cx (1 : A))
    (g := (splitTangentChart a).toRingHom) (by
    change IsUnit (splitTangentChart a
      (nodeTangentTensorFirst W cx (1 : A) * nodeTangentTensorSecond W cx (1 : A)))
    rw [map_mul, splitTangentChart_first, splitTangentChart_second, one_mul]
    exact (splitNodalTangentUnit a).isUnit)

@[simp] theorem splitTangentOpenChart_algebraMap (b : S ⊗[R] A) :
    splitTangentOpenChart a ((algebraMap (S ⊗[R] A) U) b) = splitTangentChart a b :=
  IsLocalization.Away.lift_eq _ _ _

/-- The original chart functions survive the localization comparison unchanged. -/
theorem splitTangentOpenChart_original (b : A) :
    splitTangentOpenChart a ((algebraMap (S ⊗[R] A) U) ((1 : S) ⊗ₜ[R] b)) = b := by
  simp

/-- The first-tangent/second-tangent ratio is the inverse smooth-chart Laurent unit. -/
theorem splitTangentOpenChart_parameter :
    Units.map (splitTangentOpenChart a).toMonoidHom
        (nodeTangentTensorOpenParameter W cx (1 : A)) = (splitNodalTangentUnit a)⁻¹ := by
  have h₁ : Units.map (splitTangentOpenChart a).toMonoidHom
      (nodeTangentTensorOpenFirstUnit W cx (1 : A)) = 1 := by
    apply Units.ext
    change splitTangentOpenChart a (nodeTangentTensorOpenFirstUnit W cx (1 : A) : U) = 1
    rw [nodeTangentTensorOpenFirstUnit_val, splitTangentOpenChart_algebraMap,
      splitTangentChart_first]
  have h₂ : Units.map (splitTangentOpenChart a).toMonoidHom
      (nodeTangentTensorOpenSecondUnit W cx (1 : A)) = splitNodalTangentUnit a := by
    apply Units.ext
    change splitTangentOpenChart a (nodeTangentTensorOpenSecondUnit W cx (1 : A) : U) = _
    rw [nodeTangentTensorOpenSecondUnit_val, splitTangentOpenChart_algebraMap,
      splitTangentChart_second]
  rw [nodeTangentTensorOpenParameter, map_mul, map_inv, h₁, h₂, one_mul]

end FLT.Mazur
