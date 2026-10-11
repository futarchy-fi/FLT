/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicExtensionProjection
public import Mathlib.RingTheory.Extension.Generators

/-!
# Lifting original polynomial coordinates through a formal comparison

A map of completed algebras lifts the original polynomial presentation to
the completion of any target extension. In particular one can choose the
target's infinitesimal extension, retaining all first-order relation data.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicPolynomialPresentationLift

open AdicExtensionProjection

variable {R A B ι : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (P : Algebra.Generators R A ι)
  (Q : Algebra.Extension R B) (I : Ideal A) (J : Ideal B)
  (e : AdicCompletion I A →ₐ[R] AdicCompletion J B)

/-- Choose formal representatives of the images of the original polynomial coordinates. -/
def coordinate (i : ι) : AdicCompletion (ideal Q J) Q.Ring :=
  (projection_surjective Q J (e (algebraMap A (AdicCompletion I A) (P.val i)))).choose

/-- Every chosen coordinate lifts the actual image under the given formal map. -/
theorem projection_coordinate (i : ι) :
    projection Q J (coordinate P Q I J e i) =
      e (algebraMap A (AdicCompletion I A) (P.val i)) :=
  (projection_surjective Q J (e (algebraMap A (AdicCompletion I A) (P.val i)))).choose_spec

/-- The free polynomial algebra extends the chosen formal coordinate representatives. -/
def lift : P.Ring →ₐ[R] AdicCompletion (ideal Q J) Q.Ring :=
  MvPolynomial.aeval (coordinate P Q I J e)

/-- The lifted algebra map has exactly the chosen values on polynomial variables. -/
@[simp] theorem lift_X (i : ι) :
    lift P Q I J e (MvPolynomial.X i) = coordinate P Q I J e i :=
  MvPolynomial.aeval_X _ _

/-- The lift lies over the given map of completed algebras on the entire polynomial algebra. -/
theorem projection_comp_lift :
    (projection Q J).comp (lift P Q I J e) =
      e.comp ((IsScalarTower.toAlgHom R A (AdicCompletion I A)).comp
        (MvPolynomial.aeval P.val)) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, lift_X, MvPolynomial.aeval_X]
  exact projection_coordinate P Q I J e i

/-- Evaluation of every lifted polynomial retains its original image in the source algebra. -/
theorem projection_lift (x : P.Ring) :
    projection Q J (lift P Q I J e x) =
      e (algebraMap A (AdicCompletion I A) (algebraMap P.Ring A x)) := by
  have hx := AlgHom.congr_fun (projection_comp_lift P Q I J e) x
  change projection Q J (lift P Q I J e x) =
    e (algebraMap A (AdicCompletion I A) (MvPolynomial.aeval P.val x)) at hx
  rw [P.algebraMap_apply]
  exact hx

/-- Original equations map to the kernel of the target completed presentation. -/
theorem relation_maps_to_kernel (x : P.ker) :
    lift P Q I J e x.val ∈ RingHom.ker (projection Q J).toRingHom := by
  change projection Q J (lift P Q I J e x.val) = 0
  rw [projection_lift]
  have hx : algebraMap P.Ring A x.val = 0 := x.property
  rw [hx, map_zero, map_zero]

end FLT.Mazur.AdicPolynomialPresentationLift
