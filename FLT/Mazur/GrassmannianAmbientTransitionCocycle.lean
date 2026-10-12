/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianAmbientTransition

/-!
# Rational cocycles and their determinant domains

Successive ambient changes multiply quotient basis matrices. This identifies the
triple-overlap domain in the first chart with the successive-overlap domain and
proves the rational coordinate cocycle on that actual domain.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.GrassmannianChart
variable {R : Type*} [CommRing R] {ι κ ν : Type*}
  [Fintype ι] [Fintype κ] [Fintype ν] {d : ℕ}
  (A : Matrix (Fin d) ι R)
  (e : ((Fin d → R) × (κ → R)) ≃ₗ[R] ((Fin d → R) × (ι → R)))
  (f : ((Fin d → R) × (ν → R)) ≃ₗ[R] ((Fin d → R) × (κ → R)))

omit [Fintype ν] in
/-- Successive ambient quotient basis matrices multiply on the first overlap. -/
theorem ambientBasisMatrix_comp (h : IsUnit (ambientBasisMatrix A e).det) :
    ambientBasisMatrix A (f.trans e) =
      ambientBasisMatrix A e * ambientBasisMatrix (ambientTransitionMatrix A e) f := by
  classical
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, ← ambientBasisMatrix_toLin A (f.trans e),
    ← ambientBasisMatrix_toLin A e, ← ambientBasisMatrix_toLin _ f]
  have hb := (ambientBasisMatrix_isUnit_iff A e).mp h
  simpa only [ambientTransitionMatrix_toLin A e h] using transitionBasis_comp _ e f hb

omit [Fintype ν] in
/-- On the first overlap, the third-basis determinant is a unit exactly on the next overlap. -/
theorem ambientBasisMatrix_comp_isUnit_iff (h : IsUnit (ambientBasisMatrix A e).det) :
    IsUnit (ambientBasisMatrix A (f.trans e)).det ↔
      IsUnit (ambientBasisMatrix (ambientTransitionMatrix A e) f).det := by
  rw [ambientBasisMatrix_comp A e f h, Matrix.det_mul, IsUnit.mul_iff]
  exact and_iff_right h

omit [Fintype ν] in
/-- Two successive determinant overlap conditions construct the composite condition. -/
theorem ambientBasisMatrix_comp_isUnit (h : IsUnit (ambientBasisMatrix A e).det)
    (k : IsUnit (ambientBasisMatrix (ambientTransitionMatrix A e) f).det) :
    IsUnit (ambientBasisMatrix A (f.trans e)).det :=
  (ambientBasisMatrix_comp_isUnit_iff A e f h).mpr k

/-- The actual rational transition matrices satisfy the triple-overlap cocycle. -/
theorem ambientTransitionMatrix_cocycle (h : IsUnit (ambientBasisMatrix A e).det)
    (k : IsUnit (ambientBasisMatrix (ambientTransitionMatrix A e) f).det) :
    ambientTransitionMatrix A (f.trans e) =
      ambientTransitionMatrix (ambientTransitionMatrix A e) f := by
  classical
  apply Matrix.toLin'.injective
  rw [← ambientTransitionMatrix_toLin _ _ (ambientBasisMatrix_comp_isUnit A e f h k),
    ← ambientTransitionMatrix_toLin _ _ k]
  have hb := (ambientBasisMatrix_isUnit_iff A e).mp h
  have kb : Function.Bijective (transitionBasis (chartTransition (Matrix.toLin' A) e hb) f) := by
    rw [ambientTransitionMatrix_toLin A e h]
    exact (ambientBasisMatrix_isUnit_iff _ f).mp k
  simpa only [ambientTransitionMatrix_toLin A e h] using chartTransition_cocycle _ e f hb kb

variable (S : Type*) [CommRing S] [Algebra R S]

omit A in
/-- Scalar extension respects composition of the actual ambient equivalences. -/
theorem ambientEquivBaseChange_trans :
    ambientEquivBaseChange S (f.trans e) =
      (ambientEquivBaseChange S f).trans (ambientEquivBaseChange S e) := by
  apply LinearEquiv.ext
  intro x
  simp [ambientEquivBaseChange, LinearEquiv.baseChange_trans]

end FLT.Mazur.GrassmannianChart
