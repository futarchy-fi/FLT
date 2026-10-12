/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianAmbientSecondChart
public import FLT.Mazur.GrassmannianPrincipalOverlap
public import FLT.Mazur.GrassmannianLocalizedAmbientTransition

/-!
# Affine representation of original ambient double-chart points

Every original quotient lying in two ambient charts has a unique algebra map
from their actual determinant localization. Both chart conditions refer to the
same entire original relation, without choosing an abstract replacement quotient.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R A M κ : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Fintype κ] {d : ℕ}

/-- Original ambient quotient points belonging to both specified base-changed charts. -/
def AmbientOverlapPoint (i j : AmbientChartIndex R M κ d) :=
  {N : AmbientChartPoint (ambientChartBaseChange A i) //
    Function.Bijective (N.val.toSubmodule.mkQ.comp
      (ambientChartSelected (ambientChartBaseChange A j)))}

/-- Coordinate transport identifies the split overlap with the original ambient overlap. -/
def ambientOverlapPointTransport (i j : AmbientChartIndex R M κ d) :
    PrincipalOverlapPoints (S := A) (ambientBlockP (ambientChartChange i j).toLinearMap)
      (ambientBlockQ (ambientChartChange i j).toLinearMap) ≃ AmbientOverlapPoint (A := A) i j where
  toFun N := ⟨ambientChartPointOfSplit (ambientChartBaseChange A i) N.val,
    (ambientChartPointOfSplit_baseChange_second_iff i j N.val).mpr N.property⟩
  invFun N := ⟨ambientChartPointToSplit (ambientChartBaseChange A i) N.val, by
    have h := ambientChartPointOfSplit_baseChange_second_iff i j
      (ambientChartPointToSplit (ambientChartBaseChange A i) N.val)
    rw [ambientChartPointOfSplit_toSplit] at h
    exact h.mp N.property⟩
  left_inv N := Subtype.ext (ambientChartPointToSplit_ofSplit _ N.val)
  right_inv N := Subtype.ext (ambientChartPointOfSplit_toSplit _ N.val)

/-- The actual determinant-localized algebra represents every original double-chart point. -/
def ambientOverlapPointEquiv (i j : AmbientChartIndex R M κ d) :
    (ambientOverlapRing (ambientChartChange i j) →ₐ[R] A) ≃ AmbientOverlapPoint (A := A) i j :=
  (principalOverlapPointEquiv (ambientBlockP (ambientChartChange i j).toLinearMap)
    (ambientBlockQ (ambientChartChange i j).toLinearMap)).trans (ambientOverlapPointTransport i j)

/-- Every original double-chart point has a unique localized classifying algebra map. -/
theorem ambientOverlapPoint_unique (i j : AmbientChartIndex R M κ d)
    (N : AmbientOverlapPoint (A := A) i j) :
    ∃! f : ambientOverlapRing (ambientChartChange i j) →ₐ[R] A,
      ambientOverlapPointEquiv i j f = N :=
  (ambientOverlapPointEquiv i j).bijective.existsUnique N

/-- Restriction to the polynomial ring recovers the entire first-chart quotient point. -/
theorem ambientOverlapPointEquiv_first (i j : AmbientChartIndex R M κ d)
    (f : ambientOverlapRing (ambientChartChange i j) →ₐ[R] A) :
    (ambientOverlapPointEquiv i j f).val =
      ambientChartPointOfSplit (ambientChartBaseChange A i)
        (splitChartPolynomialEquiv R A κ d (f.comp (Algebra.algHom R _ _))) := rfl

end FLT.Mazur.GrassmannianChart
