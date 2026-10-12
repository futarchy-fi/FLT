/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianAmbientTransition
public import FLT.Mazur.GrassmannianTransitionSpecialization

/-!
# Transition maps into the reverse determinant localization

An actual base-ring ambient equivalence gives a transition homomorphism between
the two determinant-localized rings. Reverse overlap membership is proved from
the inverse coordinate transition, rather than supplied as an assumption.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.GrassmannianChart
variable {R : Type*} [CommRing R] {ι κ : Type*} [Fintype ι] [Fintype κ] {d : ℕ}
  (e : ((Fin d → R) × (κ → R)) ≃ₗ[R] ((Fin d → R) × (ι → R)))

/-- The determinant overlap ring for an actual ambient change. -/
abbrev ambientOverlapRing :=
  principalOverlapRing (ambientBlockP e.toLinearMap) (ambientBlockQ e.toLinearMap)

/-- The first quotient coordinates over the determinant overlap. -/
abbrev ambientOverlapMatrix :=
  overlapUniversalMatrix (ambientBlockP e.toLinearMap) (ambientBlockQ e.toLinearMap)

/-- The first determinant is a unit after scalar extension to its principal overlap. -/
theorem ambientOverlapMatrix_isUnit :
    IsUnit (ambientBasisMatrix (ambientOverlapMatrix e)
      (ambientEquivBaseChange (ambientOverlapRing e) e)).det := by
  simpa only [ambientBasisMatrix, ambientBlockP_baseChange, ambientBlockQ_baseChange] using
    overlapUniversalMatrix_isUnit (ambientBlockP e.toLinearMap) (ambientBlockQ e.toLinearMap)

/-- The second polynomial chart maps into the first determinant overlap. -/
def ambientTransitionPolynomialHom :
    MvPolynomial (Fin d × κ) R →ₐ[R] ambientOverlapRing e :=
  localizedChartTransitionHom (ambientBlockP e.toLinearMap) (ambientBlockQ e.toLinearMap)
    (ambientBlockU e.toLinearMap) (ambientBlockT e.toLinearMap)

/-- The universal second chart has the scalar-extended ambient transition coordinates. -/
theorem ambientTransitionPolynomialHom_matrix :
    matrixPolynomialHomEquiv R (ambientOverlapRing e) κ d (ambientTransitionPolynomialHom e) =
      ambientTransitionMatrix (ambientOverlapMatrix e)
        (ambientEquivBaseChange (ambientOverlapRing e) e) := by
  rw [ambientTransitionMatrix, ambientBlockP_baseChange, ambientBlockQ_baseChange,
    ambientBlockU_baseChange, ambientBlockT_baseChange]
  ext i j
  exact localizedChartTransitionHom_entry _ _ _ _ i j

/-- The reverse defining determinant is a unit on the universal forward overlap. -/
theorem ambientTransitionPolynomialHom_reverse_isUnit :
    IsUnit (ambientTransitionPolynomialHom e
      (overlapPolynomial (ambientBlockP e.symm.toLinearMap)
        (ambientBlockQ e.symm.toLinearMap))) := by
  rw [overlapPolynomial_specialize, ambientTransitionPolynomialHom_matrix]
  have h := ambientTransitionMatrix_reverse_isUnit (ambientOverlapMatrix e)
    (ambientEquivBaseChange (ambientOverlapRing e) e) (ambientOverlapMatrix_isUnit e)
  simpa only [← ambientEquivBaseChange_symm, ambientBasisMatrix,
    ambientBlockP_baseChange, ambientBlockQ_baseChange] using h

/-- The transition extends to the actual reverse determinant localization. -/
def ambientOverlapTransitionHom : ambientOverlapRing e.symm →ₐ[R] ambientOverlapRing e :=
  IsLocalization.Away.liftAlgHom
    (overlapPolynomial (ambientBlockP e.symm.toLinearMap) (ambientBlockQ e.symm.toLinearMap))
    (ambientTransitionPolynomialHom_reverse_isUnit e)

/-- The localized transition restricts to the original polynomial classifying map. -/
theorem ambientOverlapTransitionHom_algebraMap (x : MvPolynomial (Fin d × κ) R) :
    ambientOverlapTransitionHom e (algebraMap _ (ambientOverlapRing e.symm) x) =
      ambientTransitionPolynomialHom e x := by
  exact IsLocalization.Away.lift_eq _ (ambientTransitionPolynomialHom_reverse_isUnit e) x

/-- The localized transition sends universal coordinates to the full rational transition. -/
theorem ambientOverlapTransitionHom_matrix :
    (ambientOverlapMatrix e.symm).map (ambientOverlapTransitionHom e) =
      ambientTransitionMatrix (ambientOverlapMatrix e)
        (ambientEquivBaseChange (ambientOverlapRing e) e) := by
  rw [← ambientTransitionPolynomialHom_matrix]
  ext i j
  exact ambientOverlapTransitionHom_algebraMap e (MvPolynomial.X (i, j))

end FLT.Mazur.GrassmannianChart
