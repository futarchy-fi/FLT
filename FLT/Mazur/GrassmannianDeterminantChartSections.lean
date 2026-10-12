/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianDeterminantOverlapUnits
public import FLT.Mazur.GrassmannianTripleOverlapDeterminant
public import FLT.Mazur.GrassmannianIndexedOverlapScheme

/-!
# Determinant section coordinates in every original ambient chart

For every ambient decomposition, its selected quotient determinant defines a
polynomial in each chart. These polynomials transform by the actual overlap
unit, and the distinguished coordinate in its own chart is one.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R M ι : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] {d : ℕ}

/-- The selected determinant for chart `j`, expressed in chart `i`. -/
def determinantChartSection (i j : AmbientChartIndex R M ι d) :
    MvPolynomial (Fin d × ι) R :=
  overlapPolynomial (ambientBlockP (ambientChartChange i j).toLinearMap)
    (ambientBlockQ (ambientChartChange i j).toLinearMap)

/-- The distinguished determinant is normalized to one throughout its own chart. -/
@[simp] theorem determinantChartSection_self (i : AmbientChartIndex R M ι d) :
    determinantChartSection i i = 1 := by
  unfold determinantChartSection
  rw [ambientChartChange_self]
  exact ambientOverlapPolynomial_refl

/-- Localizing the section gives exactly the overlap unit, with no discarded equations. -/
theorem determinantChartSection_overlap (i j : AmbientChartIndex R M ι d) :
    algebraMap _ (ambientOverlapRing (ambientChartChange i j))
        (determinantChartSection i j) =
      (determinantOverlapUnit (ambientChartChange i j) : _) := by
  rw [determinantOverlapUnit_val]
  exact (overlapPolynomial_specialize _ _ (Algebra.algHom R _ _)).trans (by
    congr 1
    simp only [ambientBasisMatrix, ambientBlockP_baseChange, ambientBlockQ_baseChange]
    rfl)

/-- Every selected determinant transforms by the same actual quotient-basis unit. -/
theorem determinantChartSection_transition (i j k : AmbientChartIndex R M ι d) :
    algebraMap _ (ambientOverlapRing (ambientChartChange i j))
        (determinantChartSection i k) =
      (determinantOverlapUnit (ambientChartChange i j) : _) *
        ambientTransitionPolynomialHom (ambientChartChange i j)
          (determinantChartSection j k) := by
  rw [determinantOverlapUnit_val]
  have h := tripleOverlap_compositeDeterminant
    (ambientChartChange i j) (ambientChartChange j k)
  rw [ambientChartChange_trans] at h
  exact h

/-- The reverse determinant is the inverse unit on the entire original double overlap. -/
theorem determinantChartSection_reverse (i j : AmbientChartIndex R M ι d) :
    ambientTransitionPolynomialHom (ambientChartChange i j) (determinantChartSection j i) =
      ((determinantOverlapUnit (ambientChartChange i j))⁻¹ :
        (ambientOverlapRing (ambientChartChange i j))ˣ) := by
  have h := determinantChartSection_transition i j i
  rw [determinantChartSection_self, map_one] at h
  apply (Units.mul_right_inj (determinantOverlapUnit (ambientChartChange i j))).mp
  rw [← h, Units.mul_inv]

end FLT.Mazur.GrassmannianChart
