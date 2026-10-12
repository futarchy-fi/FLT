/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianPrincipalOverlap
public import FLT.Mazur.GrassmannianBlockTransition

/-!
# Localized polynomial transition maps

On the determinant localization, the universal quotient basis matrix is invertible.
Its inverse constructs the actual polynomial classifying map for the second chart.
The full quotient relation is retained by this universal transition.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.GrassmannianChart
variable {R : Type*} [CommRing R] {ι κ : Type*} [Fintype ι] [Fintype κ] {d : ℕ}
  (P : Matrix (Fin d) (Fin d) R) (Q : Matrix ι (Fin d) R)

/-- Universal first-chart coordinates restricted to the determinant overlap. -/
def overlapUniversalMatrix : Matrix (Fin d) ι (principalOverlapRing P Q) :=
  (universalChartMatrix (R := R)).map
    (algebraMap (MvPolynomial (Fin d × ι) R) (principalOverlapRing P Q))

/-- The universal second basis determinant is a unit in the overlap coordinate ring. -/
theorem overlapUniversalMatrix_isUnit :
    IsUnit ((P.map (algebraMap R (principalOverlapRing P Q))) + overlapUniversalMatrix P Q *
      Q.map (algebraMap R (principalOverlapRing P Q))).det := by
  have h := overlapPolynomial_specialize P Q
    (Algebra.algHom R (MvPolynomial (Fin d × ι) R) (principalOverlapRing P Q))
  have hu := IsLocalization.Away.algebraMap_isUnit (S := principalOverlapRing P Q)
    (overlapPolynomial P Q)
  change IsUnit ((Algebra.algHom R _ (principalOverlapRing P Q)) (overlapPolynomial P Q)) at hu
  rw [h] at hu
  exact hu

variable (U : Matrix (Fin d) κ R) (T : Matrix ι κ R)

/-- Universal second-chart coordinates, with the determinant denominator inverted. -/
def localizedTransitionMatrix : Matrix (Fin d) κ (principalOverlapRing P Q) :=
  blockTransitionMatrix (overlapUniversalMatrix P Q)
    (P.map (algebraMap R _)) (Q.map (algebraMap R _))
    (U.map (algebraMap R _)) (T.map (algebraMap R _))

/-- The actual transition homomorphism from the second polynomial chart to the first overlap. -/
def localizedChartTransitionHom :
    MvPolynomial (Fin d × κ) R →ₐ[R] principalOverlapRing P Q :=
  MvPolynomial.aeval (fun ij ↦ localizedTransitionMatrix P Q U T ij.1 ij.2)

omit [Fintype κ] in
/-- The transition morphism sends each matrix generator to the rational matrix entry. -/
theorem localizedChartTransitionHom_entry (i : Fin d) (j : κ) :
    localizedChartTransitionHom P Q U T (MvPolynomial.X (i, j)) =
      localizedTransitionMatrix P Q U T i j := by
  simp [localizedChartTransitionHom]

/-- Its classified point has exactly the rational transition coordinates. -/
theorem localizedChartTransitionHom_coordinates :
    let _ := Classical.decEq κ
    splitChartCoordinates (splitChartPolynomialEquiv R (principalOverlapRing P Q) κ d
      (localizedChartTransitionHom P Q U T)) =
        Matrix.toLin' (localizedTransitionMatrix P Q U T) := by
  classical
  change splitChartCoordinates (splitChartOfCoordinates _) = _
  rw [splitChartCoordinates_ofCoordinates]
  apply congrArg Matrix.toLin'
  funext i j
  exact localizedChartTransitionHom_entry P Q U T i j

/-- The universal transition retains every original quotient relation under the ambient map. -/
theorem localizedChartTransitionHom_relations :
    let _ := Classical.decEq ι
    (splitChartPolynomialEquiv R (principalOverlapRing P Q) κ d
      (localizedChartTransitionHom P Q U T)).val.toSubmodule =
        (splitChartEvaluation (Matrix.toLin' (overlapUniversalMatrix P Q))).ker.comap
          (blockAmbientMap (P.map (algebraMap R _)) (Q.map (algebraMap R _))
            (U.map (algebraMap R _)) (T.map (algebraMap R _))) := by
  classical
  dsimp only
  rw [← splitChartCoordinates_kernel, localizedChartTransitionHom_coordinates]
  exact blockTransitionMatrix_kernel _ _ _ _ _ (overlapUniversalMatrix_isUnit P Q)

end FLT.Mazur.GrassmannianChart
