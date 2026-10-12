/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianSplitChartCoordinates
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Polynomial coordinates represent split Grassmannian charts

For a finite complementary basis, the split chart is parametrized by the
polynomial algebra in the matrix entries. The equivalence retains the actual
quotient relation submodule over any coefficient algebra.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.GrassmannianChart
variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  (ι : Type*) [Fintype ι] (d : ℕ)

/-- Evaluating the polynomial generators is equivalent to specifying a coordinate matrix. -/
def matrixPolynomialHomEquiv :
    (MvPolynomial (Fin d × ι) R →ₐ[R] S) ≃ Matrix (Fin d) ι S where
  toFun f i j := f (MvPolynomial.X (i, j))
  invFun A := MvPolynomial.aeval (fun ij ↦ A ij.1 ij.2)
  left_inv f := by
    apply MvPolynomial.algHom_ext
    intro ij
    simp
  right_inv A := by
    funext i j
    simp

/-- The polynomial coefficient algebra parametrizes precisely the actual split chart. -/
def splitChartPolynomialEquiv :
    (MvPolynomial (Fin d × ι) R →ₐ[R] S) ≃ SplitChart S (ι → S) d := by
  classical
  exact (matrixPolynomialHomEquiv R S ι d).trans
    (Matrix.toLin'.toEquiv.trans splitChartCoordinateEquiv)

/-- Matrix entries of the represented chart point are the images of the generators. -/
theorem splitChartPolynomialEquiv_entry
    (f : MvPolynomial (Fin d × ι) R →ₐ[R] S) (i : Fin d) (j : ι) :
    let _ := Classical.decEq ι
    LinearMap.toMatrix' (splitChartCoordinates (splitChartPolynomialEquiv R S ι d f)) i j =
      f (MvPolynomial.X (i, j)) := by
  classical
  change LinearMap.toMatrix'
    (splitChartCoordinates (splitChartOfCoordinates
      (Matrix.toLin' (matrixPolynomialHomEquiv R S ι d f)))) i j = _
  rw [splitChartCoordinates_ofCoordinates, LinearMap.toMatrix'_toLin']
  rfl

variable {R S ι d}
/-- The unique polynomial classifying map is recovered from the original quotient point. -/
theorem splitChartPolynomialEquiv_unique (N : SplitChart S (ι → S) d) :
    ∃! f : MvPolynomial (Fin d × ι) R →ₐ[R] S,
      splitChartPolynomialEquiv R S ι d f = N :=
  (splitChartPolynomialEquiv R S ι d).bijective.existsUnique N

variable (T : Type*) [CommRing T] [Algebra R T]
/-- Coefficient morphisms apply entrywise to the constructed chart coordinates. -/
theorem splitChartPolynomialEquiv_entry_natural (g : S →ₐ[R] T)
    (f : MvPolynomial (Fin d × ι) R →ₐ[R] S) (i : Fin d) (j : ι) :
    let _ := Classical.decEq ι
    LinearMap.toMatrix' (splitChartCoordinates
        (splitChartPolynomialEquiv R T ι d (g.comp f))) i j =
      g (LinearMap.toMatrix'
        (splitChartCoordinates (splitChartPolynomialEquiv R S ι d f)) i j) := by
  classical
  dsimp only
  rw [splitChartPolynomialEquiv_entry, splitChartPolynomialEquiv_entry]
  rfl

end FLT.Mazur.GrassmannianChart
