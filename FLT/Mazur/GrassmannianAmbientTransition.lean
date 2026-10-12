/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianAmbientBlocks
public import FLT.Mazur.GrassmannianChartTransitionInverse

/-!
# Rational transitions for actual ambient equivalences

The four blocks of an ambient equivalence give a rational coordinate transition.
Its reverse determinant is automatically a unit, and the reverse formula recovers
the original matrix. Thus the rational formulas have the required overlap domains.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.GrassmannianChart
variable {R : Type*} [CommRing R] {ι κ : Type*} [Fintype ι] [Fintype κ] {d : ℕ}

/-- The second quotient basis matrix of an actual ambient change. -/
def ambientBasisMatrix (A : Matrix (Fin d) ι R)
    (e : ((Fin d → R) × (κ → R)) ≃ₗ[R] ((Fin d → R) × (ι → R))) :=
  ambientBlockP e.toLinearMap + A * ambientBlockQ e.toLinearMap

/-- Rational complementary coordinates for an actual ambient change. -/
def ambientTransitionMatrix (A : Matrix (Fin d) ι R)
    (e : ((Fin d → R) × (κ → R)) ≃ₗ[R] ((Fin d → R) × (ι → R))) :=
  blockTransitionMatrix A (ambientBlockP e.toLinearMap) (ambientBlockQ e.toLinearMap)
    (ambientBlockU e.toLinearMap) (ambientBlockT e.toLinearMap)

omit [Fintype κ] in
/-- The constructed basis matrix represents the abstract quotient basis map. -/
theorem ambientBasisMatrix_toLin (A : Matrix (Fin d) ι R)
    (e : ((Fin d → R) × (κ → R)) ≃ₗ[R] ((Fin d → R) × (ι → R))) :
    let _ := Classical.decEq ι
    transitionBasis (Matrix.toLin' A) e = Matrix.toLin' (ambientBasisMatrix A e) := by
  classical
  dsimp only
  rw [ambientBasisMatrix, map_add, Matrix.toLin'_mul]
  simp only [ambientBlockP, ambientBlockQ, Matrix.toLin'_toMatrix']
  rfl

omit [Fintype κ] in
/-- Unit basis determinant is equivalent to actual quotient-basis invertibility. -/
theorem ambientBasisMatrix_isUnit_iff (A : Matrix (Fin d) ι R)
    (e : ((Fin d → R) × (κ → R)) ≃ₗ[R] ((Fin d → R) × (ι → R))) :
    let _ := Classical.decEq ι
    IsUnit (ambientBasisMatrix A e).det ↔
      Function.Bijective (transitionBasis (Matrix.toLin' A) e) := by
  classical
  dsimp only
  rw [ambientBasisMatrix_toLin, ← Module.End.isUnit_iff, LinearMap.isUnit_iff_isUnit_det]
  simp only [← LinearMap.det_toMatrix', LinearMap.toMatrix'_toLin']

/-- Rational coordinates equal the abstract transition for every invertible ambient change. -/
theorem ambientTransitionMatrix_toLin (A : Matrix (Fin d) ι R)
    (e : ((Fin d → R) × (κ → R)) ≃ₗ[R] ((Fin d → R) × (ι → R)))
    (h : IsUnit (ambientBasisMatrix A e).det) :
    let _ := Classical.decEq ι
    let _ := Classical.decEq κ
    chartTransition (Matrix.toLin' A) e ((ambientBasisMatrix_isUnit_iff A e).mp h) =
      Matrix.toLin' (ambientTransitionMatrix A e) := by
  classical
  obtain ⟨hb, he⟩ := blockTransitionMatrix_eq_chartTransition A
    (ambientBlockP e.toLinearMap) (ambientBlockQ e.toLinearMap)
    (ambientBlockU e.toLinearMap) (ambientBlockT e.toLinearMap)
    e (ambientBlocks_reconstruct e.toLinearMap).symm h
  exact he

/-- The rational forward change constructs membership in the reverse determinant overlap. -/
theorem ambientTransitionMatrix_reverse_isUnit (A : Matrix (Fin d) ι R)
    (e : ((Fin d → R) × (κ → R)) ≃ₗ[R] ((Fin d → R) × (ι → R)))
    (h : IsUnit (ambientBasisMatrix A e).det) :
    IsUnit (ambientBasisMatrix (ambientTransitionMatrix A e) e.symm).det := by
  classical
  apply (ambientBasisMatrix_isUnit_iff _ e.symm).mpr
  rw [← ambientTransitionMatrix_toLin A e h]
  exact transitionBasis_symm_bijective _ _ _

/-- Reverse rational coordinates recover every original complementary entry. -/
theorem ambientTransitionMatrix_symm (A : Matrix (Fin d) ι R)
    (e : ((Fin d → R) × (κ → R)) ≃ₗ[R] ((Fin d → R) × (ι → R)))
    (h : IsUnit (ambientBasisMatrix A e).det) :
    ambientTransitionMatrix (ambientTransitionMatrix A e) e.symm = A := by
  classical
  apply Matrix.toLin'.injective
  rw [← ambientTransitionMatrix_toLin _ e.symm (ambientTransitionMatrix_reverse_isUnit A e h)]
  simpa only [ambientTransitionMatrix_toLin A e h] using
    chartTransition_symm (Matrix.toLin' A) e ((ambientBasisMatrix_isUnit_iff A e).mp h)

end FLT.Mazur.GrassmannianChart
