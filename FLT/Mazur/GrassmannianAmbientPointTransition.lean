/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianAmbientChartPoints
public import FLT.Mazur.GrassmannianAmbientTransition
public import FLT.Mazur.GrassmannianAmbientIndexBaseChange

/-!
# Rational transitions preserve original ambient points

On every unit determinant overlap the rational transition changes the selected
quotient basis while preserving the whole original ambient relation. The change
of ambient indices agrees with scalar extension from the original base.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R M κ : Type u} [CommRing R] [AddCommGroup M] [Module R M] [Fintype κ] {d : ℕ}

omit [Fintype κ] in
/-- An abstract chart transition preserves the entire quotient in the original ambient module. -/
theorem ambientChartPointOfSplit_transition (i j : AmbientChartIndex R M κ d)
    (c : (κ → R) →ₗ[R] (Fin d → R))
    (h : Function.Bijective (transitionBasis c (ambientChartChange i j))) :
    (ambientChartPointOfSplit j
      (splitChartOfCoordinates (chartTransition c (ambientChartChange i j) h))).val =
        (ambientChartPointOfSplit i (splitChartOfCoordinates c)).val := by
  apply Module.Grassmannian.ext
  ext x
  change x ∈ (ambientTransportPoint j (splitChartGrassmannian
    (chartTransition c (ambientChartChange i j) h))).toSubmodule ↔
      x ∈ (ambientTransportPoint i (splitChartGrassmannian c)).toSubmodule
  rw [ambientTransportPoint_mem, ambientTransportPoint_mem]
  change j.symm x ∈ (splitChartEvaluation
    (chartTransition c (ambientChartChange i j) h)).ker ↔
      i.symm x ∈ (splitChartEvaluation c).ker
  rw [chartTransition_kernel]
  change ambientChartChange i j (j.symm x) ∈ (splitChartEvaluation c).ker ↔ _
  simp only [ambientChartChange, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]

/-- The rational matrix transition gives the same full original Grassmannian point. -/
theorem ambientChartPointOfSplit_rational_transition (i j : AmbientChartIndex R M κ d)
    (c : Matrix (Fin d) κ R) (h : IsUnit (ambientBasisMatrix c (ambientChartChange i j)).det) :
    let _ := Classical.decEq κ
    (ambientChartPointOfSplit j (splitChartOfCoordinates
      (Matrix.toLin' (ambientTransitionMatrix c (ambientChartChange i j))))).val =
        (ambientChartPointOfSplit i (splitChartOfCoordinates (Matrix.toLin' c))).val := by
  classical
  dsimp only
  have hm := ambientTransitionMatrix_toLin c (ambientChartChange i j) h
  exact (congrArg (fun a ↦ (ambientChartPointOfSplit j (splitChartOfCoordinates a)).val)
    hm).symm.trans (ambientChartPointOfSplit_transition i j _ _)

/-- Changing original chart indices commutes with scalar extension of the ambient module. -/
theorem ambientChartChange_baseChange (A : Type u) [CommRing A] [Algebra R A]
    (i j : AmbientChartIndex R M κ d) :
    ambientChartChange (ambientChartBaseChange A i) (ambientChartBaseChange A j) =
      ambientEquivBaseChange A (ambientChartChange i j) := by
  apply LinearEquiv.ext
  intro x
  simp only [ambientChartChange, ambientChartBaseChange, ambientEquivBaseChange,
    LinearEquiv.trans_apply, LinearEquiv.trans_symm, LinearEquiv.symm_symm,
    LinearEquiv.baseChange_trans, LinearEquiv.baseChange_symm]

/-- Every rational overlap over a coefficient algebra preserves the full original point. -/
theorem ambientChartPointOfSplit_baseChange_transition
    (A : Type u) [CommRing A] [Algebra R A] (i j : AmbientChartIndex R M κ d)
    (c : Matrix (Fin d) κ A)
    (h : IsUnit (ambientBasisMatrix c (ambientEquivBaseChange A (ambientChartChange i j))).det) :
    let _ := Classical.decEq κ
    (ambientChartPointOfSplit (ambientChartBaseChange A j) (splitChartOfCoordinates
      (Matrix.toLin' (ambientTransitionMatrix c
        (ambientEquivBaseChange A (ambientChartChange i j)))))).val =
      (ambientChartPointOfSplit (ambientChartBaseChange A i)
        (splitChartOfCoordinates (Matrix.toLin' c))).val := by
  classical
  rw [← ambientChartChange_baseChange] at h ⊢
  exact ambientChartPointOfSplit_rational_transition _ _ c h

end FLT.Mazur.GrassmannianChart
