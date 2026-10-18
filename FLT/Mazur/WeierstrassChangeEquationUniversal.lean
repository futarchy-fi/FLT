/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassChangeEquationLocus

/-!
# The universal property of the full equation comparison algebra

Algebra maps from the constructed quotient are exactly admissible changes
between the two original equations. The equivalence is natural under every
map of test algebras; the condition is proved by the quotient equations.
-/

@[expose] public noncomputable section
open WeierstrassCurve
namespace FLT.Mazur.WeierstrassChangeParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (W V : WeierstrassCurve R)
  {A : Type} [CommRing A] [Algebra R A]

/-- Every point of the constructed equation locus is a genuine admissible comparison. -/
theorem equationChange_map_equation (f : EquationRing W V →ₐ[R] A) :
    (equationChange W V).map f.toRingHom • V.map (algebraMap R A) =
      W.map (algebraMap R A) := by
  have h := congrArg (fun U : WeierstrassCurve (EquationRing W V) ↦ U.map f.toRingHom)
    (equationChange_equation W V)
  have hf : f.toRingHom.comp (algebraMap R (EquationRing W V)) = algebraMap R A :=
    f.comp_algebraMap
  simpa only [← map_variableChange, WeierstrassCurve.map_map, hf] using h

/-- Maps from the comparison algebra are determined by their entire coordinate change. -/
theorem equation_hom_ext (f g : EquationRing W V →ₐ[R] A)
    (h : (equationChange W V).map f.toRingHom = (equationChange W V).map g.toRingHom) :
    f = g := by
  apply Ideal.Quotient.algHom_ext
  apply hom_ext
  exact h

/-- Specializing a comparison extracted from a parameter recovers that exact parameter. -/
theorem equationSpecialize_map (f : EquationRing W V →ₐ[R] A) :
    equationSpecialize W V ((equationChange W V).map f.toRingHom)
      (equationChange_map_equation W V f) = f :=
  equation_hom_ext W V _ f (equationChange_specialize W V _ _)

/-- The comparison algebra represents all admissible changes, with no marking restriction. -/
def equationParameterEquiv : (EquationRing W V →ₐ[R] A) ≃
    {C : VariableChange A // C • V.map (algebraMap R A) = W.map (algebraMap R A)} where
  toFun f := ⟨(equationChange W V).map f.toRingHom, equationChange_map_equation W V f⟩
  invFun C := equationSpecialize W V C.val C.property
  left_inv := equationSpecialize_map W V
  right_inv C := Subtype.ext (equationChange_specialize W V C.val C.property)

variable {B : Type} [CommRing B] [Algebra R B]

/-- The actual comparison extracted from a parameter commutes with every test algebra map. -/
theorem equationParameterEquiv_natural (f : EquationRing W V →ₐ[R] A) (g : A →ₐ[R] B) :
    (equationParameterEquiv W V (g.comp f)).val =
      ((equationParameterEquiv W V f).val).map g.toRingHom := rfl

/-- Specialization retains the actual composite parameter under arbitrary base change. -/
theorem equationSpecialize_natural (C : VariableChange A)
    (h : C • V.map (algebraMap R A) = W.map (algebraMap R A)) (g : A →ₐ[R] B)
    (h' : C.map g.toRingHom • V.map (algebraMap R B) = W.map (algebraMap R B)) :
    g.comp (equationSpecialize W V C h) = equationSpecialize W V (C.map g.toRingHom) h' := by
  apply equation_hom_ext
  change ((equationChange W V).map (equationSpecialize W V C h).toRingHom).map
    g.toRingHom = _
  rw [equationChange_specialize, equationChange_specialize]

end FLT.Mazur.WeierstrassChangeParameter
