/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassChangeParameter
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The actual equation locus for varying full Weierstrass comparisons

Five coefficient equations cut out the locus where the universal admissible
change carries the second equation to the first. The quotient represents
this condition over every test algebra, including nonreduced algebras.
-/

@[expose] public noncomputable section
open WeierstrassCurve
namespace FLT.Mazur.WeierstrassChangeParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R]

/-- The ordered five coefficients, retaining the long Weierstrass equation. -/
def coefficients (W : WeierstrassCurve R) : Fin 5 → R :=
  ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]

omit [CommRing R] in
/-- Equality of the full coefficient tuple is equality of equations. -/
theorem coefficients_injective : Function.Injective (coefficients (R := R)) := by
  intro W V h
  ext
  all_goals first
    | exact congrFun h 0
    | exact congrFun h 1
    | exact congrFun h 2
    | exact congrFun h 3
    | exact congrFun h 4

/-- Each coefficient commutes with every original coefficient homomorphism. -/
theorem coefficients_map {A : Type} [CommRing A] (W : WeierstrassCurve R)
    (f : R →+* A) (i : Fin 5) : coefficients (W.map f) i = f (coefficients W i) := by
  fin_cases i <;> rfl

variable (W V : WeierstrassCurve R)

/-- The five actual equations imposed on the unrestricted change parameter space. -/
def equationRelation (i : Fin 5) : ParameterRing R :=
  coefficients ((change R) • (V.map (algebraMap R _))) i -
    coefficients (W.map (algebraMap R _)) i

/-- The scheme-theoretic ideal of full equation compatibility. -/
def equationIdeal : Ideal (ParameterRing R) := Ideal.span (Set.range (equationRelation W V))

/-- The coordinate algebra of the closed comparison locus. -/
abbrev EquationRing := ParameterRing R ⧸ equationIdeal W V

/-- The universal varying change on the equation locus. -/
def equationChange : VariableChange (EquationRing W V) :=
  (change R).map (Ideal.Quotient.mk _)

variable {A : Type} [CommRing A] [Algebra R A]

/-- Factoring through the equation ideal is precisely the full transformed equation identity. -/
theorem equationIdeal_le_ker_iff (f : ParameterRing R →ₐ[R] A) :
    equationIdeal W V ≤ RingHom.ker f ↔
      (change R).map f.toRingHom • V.map (algebraMap R A) = W.map (algebraMap R A) := by
  rw [equationIdeal, Ideal.span_le, Set.range_subset_iff]
  have hm (U : WeierstrassCurve R) :
      (U.map (algebraMap R (ParameterRing R))).map f.toRingHom = U.map (algebraMap R A) := by
    rw [WeierstrassCurve.map_map]
    exact congrArg U.map f.comp_algebraMap
  have hc : ((change R) • V.map (algebraMap R (ParameterRing R))).map f.toRingHom =
      (change R).map f.toRingHom • V.map (algebraMap R A) := by
    rw [← map_variableChange, hm]
  constructor
  · intro h
    apply coefficients_injective
    funext i
    have hi := h i
    change f.toRingHom (equationRelation W V i) = 0 at hi
    rw [equationRelation, map_sub, sub_eq_zero, ← coefficients_map _ f.toRingHom,
      ← coefficients_map _ f.toRingHom, hc, hm] at hi
    exact hi
  · intro h i
    change f.toRingHom (equationRelation W V i) = 0
    rw [equationRelation, map_sub, sub_eq_zero, ← coefficients_map _ f.toRingHom,
      ← coefficients_map _ f.toRingHom, hc, hm, h]

/-- The universal change satisfies the coefficient equations by construction. -/
theorem equationChange_equation :
    equationChange W V • V.map (algebraMap R (EquationRing W V)) =
      W.map (algebraMap R (EquationRing W V)) :=
  (equationIdeal_le_ker_iff W V (Ideal.Quotient.mkₐ R _)).mp
    (fun _ h ↦ Ideal.Quotient.eq_zero_iff_mem.mpr h)

/-- Every compatible change specializes the actual closed comparison algebra. -/
def equationSpecialize (C : VariableChange A)
    (h : C • V.map (algebraMap R A) = W.map (algebraMap R A)) :
    EquationRing W V →ₐ[R] A :=
  Ideal.Quotient.liftₐ _ (specialize C)
    ((equationIdeal_le_ker_iff W V _).mpr (by rw [change_specialize]; exact h))

/-- The resulting comparison parameter retains the entire original change. -/
theorem equationChange_specialize (C : VariableChange A)
    (h : C • V.map (algebraMap R A) = W.map (algebraMap R A)) :
    (equationChange W V).map (equationSpecialize W V C h).toRingHom = C := by
  rw [equationChange, VariableChange.map_map]
  exact change_specialize C

end FLT.Mazur.WeierstrassChangeParameter
