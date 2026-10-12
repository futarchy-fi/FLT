/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianChartChangeDeterminant
public import FLT.Mazur.GrassmannianChartPolynomialParameters

/-!
# The polynomial defining a Grassmannian chart overlap

Write the second selected summand in the first ambient decomposition as `(P,Q)`.
For universal complementary coordinates `X`, its quotient basis matrix is `P + XQ`.
Its determinant specializes to the actual second-chart membership criterion.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.GrassmannianChart
variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {d : ℕ}

/-- The universal matrix of complementary quotient coordinates. -/
def universalChartMatrix : Matrix (Fin d) ι (MvPolynomial (Fin d × ι) R) :=
  fun i j ↦ MvPolynomial.X (i, j)

/-- The second selected summand, specified by its two coefficient matrices. -/
def matrixSelectedSummand (P : Matrix (Fin d) (Fin d) R) (Q : Matrix ι (Fin d) R) :
    (Fin d → R) →ₗ[R] ((Fin d → R) × (ι → R)) := by
  classical
  exact (Matrix.toLin' P).prod (Matrix.toLin' Q)

/-- In normalized coordinates, the second basis matrix is `P + AQ`. -/
theorem chartChangeMap_matrixSelected (A : Matrix (Fin d) ι R)
    (P : Matrix (Fin d) (Fin d) R) (Q : Matrix ι (Fin d) R) :
    let _ := Classical.decEq ι
    chartChangeMap (Matrix.toLin' A) (matrixSelectedSummand P Q) =
      Matrix.toLin' (P + A * Q) := by
  classical
  dsimp only
  rw [map_add, Matrix.toLin'_mul]
  rfl

/-- The universal determinant polynomial for the second selected summand. -/
def overlapPolynomial (P : Matrix (Fin d) (Fin d) R) (Q : Matrix ι (Fin d) R) :
    MvPolynomial (Fin d × ι) R :=
  (P.map MvPolynomial.C + universalChartMatrix * Q.map MvPolynomial.C).det

variable {S : Type*} [CommRing S] [Algebra R S]

/-- Specialization of the universal basis matrix applies the coefficient homomorphism. -/
theorem overlapMatrix_specialize (P : Matrix (Fin d) (Fin d) R) (Q : Matrix ι (Fin d) R)
    (f : MvPolynomial (Fin d × ι) R →ₐ[R] S) :
    (P.map MvPolynomial.C + universalChartMatrix * Q.map MvPolynomial.C).map f =
      P.map (algebraMap R S) + matrixPolynomialHomEquiv R S ι d f *
        Q.map (algebraMap R S) := by
  ext i j
  simp [Matrix.map_apply, Matrix.add_apply, Matrix.mul_apply, map_sum,
    universalChartMatrix, matrixPolynomialHomEquiv]
  rfl

/-- Evaluation of the defining polynomial is exactly the second basis determinant. -/
theorem overlapPolynomial_specialize (P : Matrix (Fin d) (Fin d) R)
    (Q : Matrix ι (Fin d) R) (f : MvPolynomial (Fin d × ι) R →ₐ[R] S) :
    f (overlapPolynomial P Q) =
      (P.map (algebraMap R S) + matrixPolynomialHomEquiv R S ι d f *
        Q.map (algebraMap R S)).det := by
  rw [overlapPolynomial, AlgHom.map_det]
  exact congrArg Matrix.det (overlapMatrix_specialize P Q f)

/-- The determinant polynomial cuts out membership of the original point in the second chart. -/
theorem overlapPolynomial_isUnit_iff (P : Matrix (Fin d) (Fin d) R)
    (Q : Matrix ι (Fin d) R) (f : MvPolynomial (Fin d × ι) R →ₐ[R] S) :
    IsUnit (f (overlapPolynomial P Q)) ↔
      Function.Bijective ((splitChartPolynomialEquiv R S ι d f).val.toSubmodule.mkQ.comp
        (matrixSelectedSummand (P.map (algebraMap R S)) (Q.map (algebraMap R S)))) := by
  classical
  rw [splitChart_secondBasis_iff, overlapPolynomial_specialize, chartChangeDet_matrix]
  have hc : splitChartCoordinates (splitChartPolynomialEquiv R S ι d f) =
      Matrix.toLin' (matrixPolynomialHomEquiv R S ι d f) :=
    splitChartCoordinates_ofCoordinates _
  rw [hc, chartChangeMap_matrixSelected, LinearMap.toMatrix'_toLin']

end FLT.Mazur.GrassmannianChart
