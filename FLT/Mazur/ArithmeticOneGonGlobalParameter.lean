/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonAlgebraicFamily

/-!
# Arithmetic degeneration parameters on arbitrary schemes

The fixed algebraic parameter scheme represents global sections satisfying the
open discriminant-factor condition, also on nonaffine and nonreduced bases.
The independently constructed arithmetic family is its full curve pullback.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.ArithmeticOneGonParameter
open GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {T U : Scheme.{0}}

/-- The original normalized pullback on coefficient functions. -/
def coefficients (f : T ⟶ parameterBase) : ParameterRing →+* Γ(T, ⊤) :=
  ((Scheme.ΓSpecIso (.of ParameterRing)).inv ≫ f.appTop).hom

/-- A global parameter defines a morphism to the fixed integral parameter scheme. -/
def globalParameterMap (t : Γ(T, ⊤)) (ht : IsUnit (1 + 432 * t)) : T ⟶ parameterBase :=
  T.toSpecΓ ≫ parameterMap t ht

/-- Global classification retains precisely the prescribed coefficient homomorphism. -/
theorem globalParameterMap_coefficients (t : Γ(T, ⊤)) (ht : IsUnit (1 + 432 * t)) :
    coefficients (globalParameterMap t ht) = specialize t ht :=
  congrArg CommRingCat.Hom.hom
    (ΓSpecIso_inv_ΓSpec_adjunction_homEquiv (CommRingCat.ofHom (specialize t ht)))

/-- A scheme morphism into the parameter base is determined by its original parameter. -/
theorem parameterMap_ext (f g : T ⟶ parameterBase)
    (h : coefficients f parameter = coefficients g parameter) : f = g := by
  apply ext_to_Spec
  apply CommRingCat.hom_ext
  exact hom_ext _ _ h

/-- The arithmetic algebraic base represents permitted parameters on every original scheme. -/
def globalParameterEquiv : (T ⟶ parameterBase) ≃
    {t : Γ(T, ⊤) // IsUnit (1 + 432 * t)} where
  toFun f := ⟨coefficients f parameter, hom_factor_isUnit (coefficients f)⟩
  invFun t := globalParameterMap t.val t.property
  left_inv f := by
    apply parameterMap_ext _ f
    rw [globalParameterMap_coefficients, specialize_parameter]
  right_inv t := by
    apply Subtype.ext
    exact (congrArg (fun f ↦ f parameter)
      (globalParameterMap_coefficients t.val t.property)).trans (specialize_parameter _ _)

/-- Pullback of the exact original parameter gives the exact composite classifying map. -/
@[reassoc] theorem globalParameterMap_natural (t : Γ(T, ⊤))
    (ht : IsUnit (1 + 432 * t)) (g : U ⟶ T)
    (hg : IsUnit (1 + 432 * g.appTop.hom t)) :
    g ≫ globalParameterMap t ht = globalParameterMap (g.appTop.hom t) hg := by
  unfold globalParameterMap parameterMap
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp]
  congr 2
  exact CommRingCat.hom_ext (specialize_natural t ht g.appTop.hom hg)

/-- The arithmetic family defined independently using the ring of original global sections. -/
def globalCurve (t : Γ(T, ⊤)) (ht : IsUnit (1 + 432 * t)) : GeneralizedEllipticCurve T :=
  (ArithmeticOneGonGeneralizedCurve.curve t ht).baseChange T.toSpecΓ

/-- The independent global family is the full generalized-curve pullback from the fixed base. -/
irreducible_def globalSpecializationIso (t : Γ(T, ⊤)) (ht : IsUnit (1 + 432 * t)) :
    globalCurve t ht ≅ universalCurve.baseChange (globalParameterMap t ht) :=
  (baseChangeFunctor T.toSpecΓ).mapIso (specializationIso t ht) ≪≫
    (universalCurve.baseChangeCompIso (parameterMap t ht) T.toSpecΓ).symm

end FLT.Mazur.ArithmeticOneGonParameter
