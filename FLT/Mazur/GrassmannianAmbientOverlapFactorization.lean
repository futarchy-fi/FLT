/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianAmbientOverlapPoints
public import FLT.Mazur.GrassmannianAmbientOverlapRepresentation

/-!
# Factoring both original chart classifications through their overlap

The localized classifying map constructed from arbitrary double-chart membership
recovers both original classifying morphisms: the first by the open inclusion,
the second by the actual rational transition.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R A M κ : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Fintype κ] {d : ℕ}

/-- Testing the universal first overlap morphism recovers its original ambient point. -/
theorem ambientOverlapFirstPoint_test (i j : AmbientChartIndex R M κ d)
    (f : ambientOverlapRing (ambientChartChange i j) →ₐ[R] A) :
    ambientChartSchemePointEquiv i
      (splitChartSchemePointMap f (ambientOverlapFirstPoint i j)) =
        (ambientOverlapPointEquiv i j f).val := by
  change ambientChartPointOfSplit _ (splitChartPolynomialEquiv R A κ d
    (Spec.homEquivAlgHom (splitChartSchemePointMap f (ambientOverlapFirstPoint i j)))) = _
  rw [splitChartSchemePointMap_algHom]
  change ambientChartPointOfSplit _ (splitChartPolynomialEquiv R A κ d
    (f.comp (Spec.homEquivAlgHom (Spec.homEquivAlgHom.symm _)))) = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- The unique algebra map from the actual overlap for an arbitrary original double-chart point. -/
def ambientOverlapClassifyingHom (i j : AmbientChartIndex R M κ d)
    (N : AmbientOverlapPoint (A := A) i j) :
    ambientOverlapRing (ambientChartChange i j) →ₐ[R] A :=
  (ambientOverlapPointEquiv i j).symm N

/-- The first original classification factors through the actual determinant open inclusion. -/
theorem ambientOverlapClassifyingHom_first (i j : AmbientChartIndex R M κ d)
    (N : AmbientOverlapPoint (A := A) i j) :
    splitChartSchemePointMap (ambientOverlapClassifyingHom i j N)
      (ambientOverlapFirstPoint i j) = (ambientChartSchemePointEquiv i).symm N.val := by
  apply (ambientChartSchemePointEquiv i).injective
  rw [ambientOverlapFirstPoint_test, Equiv.apply_symm_apply]
  exact congrArg Subtype.val ((ambientOverlapPointEquiv i j).apply_symm_apply N)

/-- The same original quotient considered as a point in the second chart. -/
def ambientOverlapSecondChartPoint (i j : AmbientChartIndex R M κ d)
    (N : AmbientOverlapPoint (A := A) i j) : AmbientChartPoint (ambientChartBaseChange A j) :=
  ⟨N.val.val, N.property⟩

/-- The second original classification factors through the actual rational transition. -/
theorem ambientOverlapClassifyingHom_second (i j : AmbientChartIndex R M κ d)
    (N : AmbientOverlapPoint (A := A) i j) :
    splitChartSchemePointMap (ambientOverlapClassifyingHom i j N)
      (ambientOverlapSecondPoint i j) =
        (ambientChartSchemePointEquiv j).symm (ambientOverlapSecondChartPoint i j N) := by
  apply (ambientChartSchemePointEquiv j).injective
  apply Subtype.ext
  rw [ambientOverlap_classifications_test_eq, ambientOverlapClassifyingHom_first]
  exact (congrArg Subtype.val ((ambientChartSchemePointEquiv i).apply_symm_apply N.val)).trans
    (congrArg Subtype.val ((ambientChartSchemePointEquiv j).apply_symm_apply
      (ambientOverlapSecondChartPoint i j N))).symm

end FLT.Mazur.GrassmannianChart
