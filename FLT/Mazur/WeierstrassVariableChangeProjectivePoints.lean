/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassVariableChangeCubicSubstitution
public import FLT.Mazur.ProjectiveHomogeneousPointTransport

/-!
# Actual projective points under admissible coordinate changes

The linear isomorphism transports evaluated scheme points by the original
homogeneous formulas, over arbitrary coefficient algebras.
-/

@[expose] public noncomputable section

open WeierstrassCurve MvPolynomial AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassVariableChangeLinear

attribute [local instance] MvPolynomial.gradedAlgebra
variable {R S : Type} [CommRing R] [CommRing S] (C : VariableChange R)
  (f : R →+* S) (P : Fin 3 → S)

/-- Evaluation of the graded substitution is the transformed coordinate evaluation. -/
theorem evaluation_comp :
    (eval₂Hom f P).comp (ProjectiveSpace.linearGradedMap (linearMap C)).toRingHom =
      eval₂Hom f (WeierstrassVariableChangeHomogeneous.coordinates (C.map f) P) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [ProjectiveSpace.linearGradedMap, ProjectiveSpace.linearSubstitution]
  · intro i
    change eval₂Hom f P (ProjectiveSpace.linearSubstitution (linearMap C) (X i)) = _
    rw [substitution_X]
    fin_cases i <;>
      simp [WeierstrassVariableChangeHomogeneous.coordinates, VariableChange.map]

/-- The actual projective scheme isomorphism has the expected homogeneous point formula. -/
theorem unitChartPoint_projectiveIso (i j : Fin 3) (a b : Sˣ) (hi : P i = a)
    (hj : WeierstrassVariableChangeHomogeneous.coordinates (C.map f) P j = b) :
    ProjectiveSpace.unitChartPoint R (Fin 3) f P i a hi ≫ (projectiveIso C).hom =
      ProjectiveSpace.unitChartPoint R (Fin 3) f
        (WeierstrassVariableChangeHomogeneous.coordinates (C.map f) P) j b hj :=
  ProjectiveSpace.unitChartPoint_linearIso_of_eval (linearEquiv C).symm f P _
    (evaluation_comp C f P) i j a b hi hj

end FLT.Mazur.WeierstrassVariableChangeLinear
