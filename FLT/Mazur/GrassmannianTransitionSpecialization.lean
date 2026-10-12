/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianLocalizedTransition

/-!
# Specialization of rational Grassmannian transitions

On the determinant overlap the inverse matrix specializes under arbitrary ring maps.
Consequently every rational transition entry specializes to the transition of the
specialized coordinates, including maps out of the universal localized chart.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.GrassmannianChart
variable {R S : Type*} [CommRing R] [CommRing S]
  {ι κ : Type*} [Fintype ι] [Fintype κ] {d : ℕ}

/-- Inverse basis matrices specialize whenever their determinant is a unit. -/
theorem overlapMatrix_inverse_map (f : R →+* S) (M : Matrix (Fin d) (Fin d) R)
    (h : IsUnit M.det) : M⁻¹.map f = (M.map f)⁻¹ := by
  apply Eq.symm
  apply Matrix.inv_eq_left_inv
  rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul]
  rw [Matrix.nonsing_inv_mul _ h, map_one]

omit [Fintype κ] in
/-- Rational coordinate changes commute with coefficient homomorphisms on their domain. -/
theorem blockTransitionMatrix_map (f : R →+* S) (A : Matrix (Fin d) ι R)
    (P : Matrix (Fin d) (Fin d) R) (Q : Matrix ι (Fin d) R)
    (U : Matrix (Fin d) κ R) (T : Matrix ι κ R) (h : IsUnit (P + A * Q).det) :
    (blockTransitionMatrix A P Q U T).map f =
      blockTransitionMatrix (A.map f) (P.map f) (Q.map f) (U.map f) (T.map f) := by
  simp only [blockTransitionMatrix, Matrix.map_mul,
    overlapMatrix_inverse_map f _ h, Matrix.map_add f f.map_add]

variable [Algebra R S]
  (P : Matrix (Fin d) (Fin d) R) (Q : Matrix ι (Fin d) R)
  (U : Matrix (Fin d) κ R) (T : Matrix ι κ R)

/-- Universal first coordinates specialize to the classified matrix of the restricted map. -/
theorem overlapUniversalMatrix_map (f : principalOverlapRing P Q →ₐ[R] S) :
    (overlapUniversalMatrix P Q).map f =
      matrixPolynomialHomEquiv R S ι d (f.comp (Algebra.algHom R _ _)) := by
  ext i j
  rfl

omit [Fintype κ] in
/-- Universal rational transition matrices specialize to the rational formula. -/
theorem localizedTransitionMatrix_map (f : principalOverlapRing P Q →ₐ[R] S) :
    (localizedTransitionMatrix P Q U T).map f =
      blockTransitionMatrix
        (matrixPolynomialHomEquiv R S ι d (f.comp (Algebra.algHom R _ _)))
        (P.map (algebraMap R S)) (Q.map (algebraMap R S))
        (U.map (algebraMap R S)) (T.map (algebraMap R S)) := by
  have h := blockTransitionMatrix_map f.toRingHom (overlapUniversalMatrix P Q)
    (P.map (algebraMap R _)) (Q.map (algebraMap R _))
    (U.map (algebraMap R _)) (T.map (algebraMap R _)) (overlapUniversalMatrix_isUnit P Q)
  change (localizedTransitionMatrix P Q U T).map f =
    blockTransitionMatrix ((overlapUniversalMatrix P Q).map f)
      ((P.map (algebraMap R _)).map f) ((Q.map (algebraMap R _)).map f)
      ((U.map (algebraMap R _)).map f) ((T.map (algebraMap R _)).map f) at h
  simpa only [Matrix.map_map, Function.comp_def,
    AlgHom.commutes, overlapUniversalMatrix_map] using h

omit [Fintype κ] in
/-- The polynomial classifying map specializes entrywise to the same rational transition. -/
theorem localizedChartTransitionHom_specialize (f : principalOverlapRing P Q →ₐ[R] S) :
    matrixPolynomialHomEquiv R S κ d (f.comp (localizedChartTransitionHom P Q U T)) =
      blockTransitionMatrix
        (matrixPolynomialHomEquiv R S ι d (f.comp (Algebra.algHom R _ _)))
        (P.map (algebraMap R S)) (Q.map (algebraMap R S))
        (U.map (algebraMap R S)) (T.map (algebraMap R S)) := by
  rw [← localizedTransitionMatrix_map]
  ext i j
  change f (localizedChartTransitionHom P Q U T (MvPolynomial.X (i, j))) = _
  rw [localizedChartTransitionHom_entry]
  rfl

end FLT.Mazur.GrassmannianChart
