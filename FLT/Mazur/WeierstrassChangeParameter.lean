/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# An affine parameter algebra for all admissible Weierstrass changes

The ring R[u,r,s,t,1/u] represents the entire change of variables, with no
restriction on the characteristic or on nilpotents in the test algebra.
-/

@[expose] public noncomputable section
open MvPolynomial WeierstrassCurve
namespace FLT.Mazur.WeierstrassChangeParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (R : Type) [CommRing R]

/-- The four independent change coordinates. -/
abbrev PolynomialRing := MvPolynomial (Fin 4) R

/-- Inverting precisely the scale coordinate gives the change parameter ring. -/
abbrev ParameterRing := Localization.Away (X (0 : Fin 4) : PolynomialRing R)

/-- The actual universal invertible scale. -/
def scale : (ParameterRing R)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (X (0 : Fin 4) : PolynomialRing R)).unit

/-- The universal unrestricted admissible change. -/
def change : VariableChange (ParameterRing R) :=
  ⟨scale R, algebraMap (PolynomialRing R) _ (X 1),
    algebraMap (PolynomialRing R) _ (X 2), algebraMap (PolynomialRing R) _ (X 3)⟩

/-- The scale is the original first polynomial coordinate. -/
theorem scale_val : (scale R : ParameterRing R) =
    algebraMap (PolynomialRing R) _ (X (0 : Fin 4)) :=
  IsUnit.unit_spec _

variable {R} {A : Type} [CommRing A] [Algebra R A]

/-- Every change gives its actual unique parameter algebra map. -/
def specialize (C : VariableChange A) : ParameterRing R →ₐ[R] A :=
  IsLocalization.Away.liftAlgHom (f := aeval ![(C.u : A), C.r, C.s, C.t])
    (X (0 : Fin 4)) (by simp)

/-- Specialization keeps the four prescribed coordinates. -/
@[simp] theorem specialize_coordinate (C : VariableChange A) (i : Fin 4) :
    specialize (R := R) C (algebraMap (PolynomialRing R) _ (X i)) =
      ![(C.u : A), C.r, C.s, C.t] i := by
  rw [specialize, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  exact aeval_X _ _

/-- The universal change specializes to exactly the given change. -/
theorem change_specialize (C : VariableChange A) :
    (change R).map (specialize (R := R) C).toRingHom = C := by
  ext
  · change specialize C (scale R : ParameterRing R) = (C.u : A)
    rw [scale_val, specialize_coordinate]
    rfl
  all_goals simp [change, VariableChange.map]

/-- Two maps out of the change ring agree as soon as their full changes agree. -/
theorem hom_ext (f g : ParameterRing R →ₐ[R] A)
    (h : (change R).map f.toRingHom = (change R).map g.toRingHom) : f = g := by
  apply IsLocalization.algHom_ext (Submonoid.powers (X (0 : Fin 4) : PolynomialRing R))
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · have hu := congrArg (fun C : VariableChange A ↦ (C.u : A)) h
    change f (scale R : ParameterRing R) = g (scale R : ParameterRing R) at hu
    rw [scale_val] at hu
    exact hu
  · exact congrArg VariableChange.r h
  · exact congrArg VariableChange.s h
  · exact congrArg VariableChange.t h

/-- The actual affine representability bijection, including arbitrary nonreduced tests. -/
def parameterEquiv : (ParameterRing R →ₐ[R] A) ≃ VariableChange A where
  toFun f := (change R).map f.toRingHom
  invFun := specialize
  left_inv f := hom_ext _ f (change_specialize _)
  right_inv := change_specialize

end FLT.Mazur.WeierstrassChangeParameter
