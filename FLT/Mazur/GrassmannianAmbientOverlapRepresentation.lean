/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianAmbientChartNaturality
public import FLT.Mazur.GrassmannianAmbientPointTransition
public import FLT.Mazur.GrassmannianOverlapTransitionScheme

/-!
# Agreement of ambient quotient classifications on determinant overlaps

The two actual scheme morphisms from each universal determinant overlap classify
the same original ambient quotient. Naturality gives agreement after every
coefficient algebra map, retaining the whole original Grassmannian point.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R A M κ : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Fintype κ] {d : ℕ}

/-- The chart point of an algebra classifying map has its explicit ambient matrix coordinates. -/
theorem ambientChartSchemePointEquiv_ofAlgHom (i : AmbientChartIndex R M κ d)
    (f : MvPolynomial (Fin d × κ) R →ₐ[R] A) :
    let _ := Classical.decEq κ
    ambientChartSchemePointEquiv i (Spec.homEquivAlgHom.symm f) =
      ambientPointOfCoordinates i (Matrix.toLin' (matrixPolynomialHomEquiv R A κ d f)) := by
  classical
  change ambientChartPointOfSplit _ (splitChartPolynomialEquiv R A κ d
    (Spec.homEquivAlgHom (Spec.homEquivAlgHom.symm f))) = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- The first actual classifying morphism on a universal original-index overlap. -/
def ambientOverlapFirstPoint (i j : AmbientChartIndex R M κ d) :
    {p : Spec (.of (ambientOverlapRing (ambientChartChange i j))) ⟶ splitChartScheme R κ d //
      p ≫ splitChartStructure R κ d =
        Spec.algebraMap R (ambientOverlapRing (ambientChartChange i j))} :=
  Spec.homEquivAlgHom.symm (IsScalarTower.toAlgHom R (MvPolynomial (Fin d × κ) R)
    (ambientOverlapRing (ambientChartChange i j)))

/-- The second actual classifying morphism uses the rational overlap transition. -/
def ambientOverlapSecondPoint (i j : AmbientChartIndex R M κ d) :
    {p : Spec (.of (ambientOverlapRing (ambientChartChange i j))) ⟶ splitChartScheme R κ d //
      p ≫ splitChartStructure R κ d =
        Spec.algebraMap R (ambientOverlapRing (ambientChartChange i j))} :=
  Spec.homEquivAlgHom.symm (ambientTransitionPolynomialHom (ambientChartChange i j))

/-- The first classifying morphism is the original determinant open inclusion. -/
theorem ambientOverlapFirstPoint_val (i j : AmbientChartIndex R M κ d) :
    (ambientOverlapFirstPoint i j).val =
      principalOverlapInclusion (ambientBlockP (ambientChartChange i j).toLinearMap)
        (ambientBlockQ (ambientChartChange i j).toLinearMap) := rfl

/-- The second classifying morphism is the original rational scheme transition. -/
theorem ambientOverlapSecondPoint_val (i j : AmbientChartIndex R M κ d) :
    (ambientOverlapSecondPoint i j).val =
      localizedChartTransitionScheme (ambientBlockP (ambientChartChange i j).toLinearMap)
        (ambientBlockQ (ambientChartChange i j).toLinearMap)
        (ambientBlockU (ambientChartChange i j).toLinearMap)
        (ambientBlockT (ambientChartChange i j).toLinearMap) := rfl

/-- Both universal overlap morphisms represent precisely the same full original quotient. -/
theorem ambientOverlap_classifications_eq (i j : AmbientChartIndex R M κ d) :
    (ambientChartSchemePointEquiv j (ambientOverlapSecondPoint i j)).val =
      (ambientChartSchemePointEquiv i (ambientOverlapFirstPoint i j)).val := by
  classical
  have hs := ambientChartSchemePointEquiv_ofAlgHom j
    (ambientTransitionPolynomialHom (ambientChartChange i j))
  have hf := ambientChartSchemePointEquiv_ofAlgHom i
    (IsScalarTower.toAlgHom R (MvPolynomial (Fin d × κ) R)
      (ambientOverlapRing (ambientChartChange i j)))
  refine (congrArg Subtype.val hs).trans (Eq.trans ?_ (congrArg Subtype.val hf).symm)
  have hm := ambientTransitionPolynomialHom_matrix (ambientChartChange i j)
  refine (congrArg (fun c ↦ (ambientPointOfCoordinates j (Matrix.toLin' c)).val) hm).trans ?_
  exact ambientChartPointOfSplit_baseChange_transition _ i j _
    (ambientOverlapMatrix_isUnit (ambientChartChange i j))

/-- Agreement holds on every affine test of the entire determinant overlap. -/
theorem ambientOverlap_classifications_test_eq (i j : AmbientChartIndex R M κ d)
    (f : ambientOverlapRing (ambientChartChange i j) →ₐ[R] A) :
    (ambientChartSchemePointEquiv j
      (splitChartSchemePointMap f (ambientOverlapSecondPoint i j))).val =
        (ambientChartSchemePointEquiv i
          (splitChartSchemePointMap f (ambientOverlapFirstPoint i j))).val := by
  rw [ambientChartSchemePointEquiv_natural_val, ambientChartSchemePointEquiv_natural_val,
    ambientOverlap_classifications_eq]

end FLT.Mazur.GrassmannianChart
