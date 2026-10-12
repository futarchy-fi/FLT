/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianAmbientTransition
public import FLT.Mazur.GrassmannianTransitionSpecialization

/-!
# Naturality of ambient rational transitions

For a fixed ambient decomposition over the base, the rational transition over
any algebra commutes with maps of algebras on the determinant overlap.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.GrassmannianChart
variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] {ι κ : Type*} [Fintype ι] [Fintype κ] {d : ℕ}

/-- Rational ambient transitions are natural under arbitrary coefficient algebra maps. -/
theorem ambientTransitionMatrix_algHom (f : S →ₐ[R] T) (A : Matrix (Fin d) ι S)
    (e : ((Fin d → R) × (κ → R)) ≃ₗ[R] ((Fin d → R) × (ι → R)))
    (h : IsUnit (ambientBasisMatrix A (ambientEquivBaseChange S e)).det) :
    (ambientTransitionMatrix A (ambientEquivBaseChange S e)).map f =
      ambientTransitionMatrix (A.map f) (ambientEquivBaseChange T e) := by
  simp only [ambientBasisMatrix, ambientBlockP_baseChange, ambientBlockQ_baseChange] at h
  simp only [ambientTransitionMatrix, ambientBlockP_baseChange, ambientBlockQ_baseChange,
    ambientBlockU_baseChange, ambientBlockT_baseChange]
  have hm := blockTransitionMatrix_map f.toRingHom A
    ((ambientBlockP e.toLinearMap).map (algebraMap R S))
    ((ambientBlockQ e.toLinearMap).map (algebraMap R S))
    ((ambientBlockU e.toLinearMap).map (algebraMap R S))
    ((ambientBlockT e.toLinearMap).map (algebraMap R S)) h
  have hf : (f.toRingHom : S → T) ∘ algebraMap R S = algebraMap R T :=
    funext f.commutes
  simp only [Matrix.map_map, hf] at hm
  exact hm

/-- The determinant overlap itself is preserved by coefficient algebra maps. -/
theorem ambientBasisMatrix_algHom (f : S →ₐ[R] T) (A : Matrix (Fin d) ι S)
    (e : ((Fin d → R) × (κ → R)) ≃ₗ[R] ((Fin d → R) × (ι → R))) :
    (ambientBasisMatrix A (ambientEquivBaseChange S e)).map f =
      ambientBasisMatrix (A.map f) (ambientEquivBaseChange T e) := by
  simp only [ambientBasisMatrix, ambientBlockP_baseChange, ambientBlockQ_baseChange,
    Matrix.map_add f f.map_add, Matrix.map_mul, Matrix.map_map, Function.comp_def,
    AlgHom.commutes]

/-- Naturality includes the domain condition, without any flatness hypothesis. -/
theorem ambientBasisMatrix_isUnit_algHom (f : S →ₐ[R] T) (A : Matrix (Fin d) ι S)
    (e : ((Fin d → R) × (κ → R)) ≃ₗ[R] ((Fin d → R) × (ι → R)))
    (h : IsUnit (ambientBasisMatrix A (ambientEquivBaseChange S e)).det) :
    IsUnit (ambientBasisMatrix (A.map f) (ambientEquivBaseChange T e)).det := by
  rw [← ambientBasisMatrix_algHom f A e]
  change IsUnit (f.mapMatrix (ambientBasisMatrix A (ambientEquivBaseChange S e))).det
  rw [← AlgHom.map_det]
  exact h.map f

end FLT.Mazur.GrassmannianChart
