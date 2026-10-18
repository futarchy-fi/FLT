/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassChangeEquationUniversal

/-!
# Coefficient base change of the full equation comparison functor

Changing the coefficient base retains every admissible comparison on every
test algebra. The coordinate maps and their naturality come from the proved
universal property of the five-equation quotient.
-/

@[expose] public noncomputable section
open WeierstrassCurve
namespace FLT.Mazur.WeierstrassChangeParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
  (W V : WeierstrassCurve R)
local notation "W'" => W.map (algebraMap R A)
local notation "V'" => V.map (algebraMap R A)

/-- The comparison equation is unchanged by an arbitrary tower of coefficient algebras. -/
theorem coefficientComparison_iff (C : VariableChange B) :
    C • (V').map (algebraMap A B) = (W').map (algebraMap A B) ↔
      C • V.map (algebraMap R B) = W.map (algebraMap R B) := by
  rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map,
    ← IsScalarTower.algebraMap_eq R A B]

/-- Full comparison parameters before and after coefficient base change classify the same tests. -/
def coefficientParameterEquiv :
    (EquationRing W' V' →ₐ[A] B) ≃ (EquationRing W V →ₐ[R] B) :=
  (equationParameterEquiv W' V').trans
    ((Equiv.subtypeEquivRight (coefficientComparison_iff W V)).trans
      (equationParameterEquiv W V).symm)

/-- The equivalence preserves the entire admissible coordinate change exactly. -/
theorem coefficientParameterEquiv_change (f : EquationRing W' V' →ₐ[A] B) :
    (equationChange W V).map (coefficientParameterEquiv W V f).toRingHom =
      (equationChange W' V').map f.toRingHom :=
  equationChange_specialize W V _ ((coefficientComparison_iff W V _).mp
    (equationChange_map_equation W' V' f))

variable {D : Type} [CommRing D] [Algebra R D] [Algebra A D] [IsScalarTower R A D]

/-- Every map of test algebras commutes with the coefficient-base-change classification. -/
theorem coefficientParameterEquiv_natural (f : EquationRing W' V' →ₐ[A] B)
    (g : B →ₐ[A] D) :
    coefficientParameterEquiv W V (g.comp f) =
      (g.restrictScalars R).comp (coefficientParameterEquiv W V f) := by
  apply equation_hom_ext
  rw [coefficientParameterEquiv_change]
  change ((equationChange W' V').map f.toRingHom).map g.toRingHom =
    ((equationChange W V).map (coefficientParameterEquiv W V f).toRingHom).map g.toRingHom
  rw [coefficientParameterEquiv_change]

end FLT.Mazur.WeierstrassChangeParameter
