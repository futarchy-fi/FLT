/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassVariableChangeLinear
public import FLT.Mazur.ProjectiveLinearCoefficientChange

/-!
# Admissible projective changes commute with coefficient maps

The actual homogeneous coordinate substitution commutes with every ring map.
Consequently its projective isomorphism retains the original coefficient map,
including under residue specialization and nilpotent thickening.
-/

@[expose] public noncomputable section
open WeierstrassCurve CategoryTheory
namespace FLT.Mazur.WeierstrassVariableChangeLinear
open ProjectiveSpace
variable {R S : Type} [CommRing R] [CommRing S] (C : VariableChange R) (f : R →+* S)

/-- The complete homogeneous linear substitution commutes with every coefficient homomorphism. -/
theorem linearEquiv_coefficient (v : Fin 3 →₀ R) :
    changeCoefficients f (linearEquiv C v) =
      linearEquiv (C.map f) (changeCoefficients f v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single i r =>
    fin_cases i <;> ext j <;> fin_cases j <;>
      simp [linearEquiv, linearMap, columns, Finsupp.linearCombination_single,
        changeCoefficients, Finsupp.smul_single, VariableChange.map, map_add, map_mul, map_pow]

/-- The actual projective coordinate change commutes with the original coefficient map. -/
@[reassoc] theorem projectiveIso_coefficient :
    coefficientMap f (Fin 3) ≫ (projectiveIso C).hom =
      (projectiveIso (C.map f)).hom ≫ coefficientMap f (Fin 3) := by
  apply linearIso_coefficientMap
  exact changeCoefficients_inverse f _ _ (linearEquiv_coefficient C f)

end FLT.Mazur.WeierstrassVariableChangeLinear
