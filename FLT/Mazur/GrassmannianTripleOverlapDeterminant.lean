/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianTripleOverlapCoordinates
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Comparing the successive and original triple domains

On the first overlap, the composite determinant is the first unit determinant
times the next pulled-back determinant. Thus their basic opens agree as opens
of the actual overlap spectrum, not only on field-valued points.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.GrassmannianChart
variable {R : Type*} [CommRing R] {ι κ ν : Type*}
  [Fintype ι] [Fintype κ] [Finite ν] {d : ℕ}
  (e : ((Fin d → R) × (κ → R)) ≃ₗ[R] ((Fin d → R) × (ι → R)))
  (f : ((Fin d → R) × (ν → R)) ≃ₗ[R] ((Fin d → R) × (κ → R)))

/-- The composite determinant factors on the entire first determinant overlap. -/
theorem tripleOverlap_compositeDeterminant :
    algebraMap _ (ambientOverlapRing e)
      (overlapPolynomial (ambientBlockP (f.trans e).toLinearMap)
        (ambientBlockQ (f.trans e).toLinearMap)) =
      (ambientBasisMatrix (ambientOverlapMatrix e)
        (ambientEquivBaseChange (ambientOverlapRing e) e)).det * tripleOverlapElement e f := by
  let _ := Fintype.ofFinite ν
  have hc := overlapPolynomial_specialize
    (ambientBlockP (f.trans e).toLinearMap) (ambientBlockQ (f.trans e).toLinearMap)
    (Algebra.algHom R _ (ambientOverlapRing e))
  have hn := overlapPolynomial_specialize (ambientBlockP f.toLinearMap)
    (ambientBlockQ f.toLinearMap) (ambientTransitionPolynomialHom e)
  rw [ambientTransitionPolynomialHom_matrix] at hn
  change tripleOverlapElement e f = _ at hn
  change algebraMap _ (ambientOverlapRing e) _ = _ at hc
  have hm : matrixPolynomialHomEquiv R (ambientOverlapRing e) ι d
      (Algebra.algHom R _ _) = ambientOverlapMatrix e := by
    ext i j
    rfl
  rw [hc, hn, hm]
  have h := ambientBasisMatrix_comp (ambientOverlapMatrix e)
    (ambientEquivBaseChange (ambientOverlapRing e) e)
    (ambientEquivBaseChange (ambientOverlapRing e) f) (ambientOverlapMatrix_isUnit e)
  rw [← ambientEquivBaseChange_trans] at h
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul] at hd
  simpa only [ambientBasisMatrix, ambientBlockP_baseChange, ambientBlockQ_baseChange] using hd

/-- The composite and successive determinants define the same open of the first overlap. -/
theorem tripleOverlap_compositeBasicOpen :
    PrimeSpectrum.basicOpen (algebraMap _ (ambientOverlapRing e)
      (overlapPolynomial (ambientBlockP (f.trans e).toLinearMap)
        (ambientBlockQ (f.trans e).toLinearMap))) =
      PrimeSpectrum.basicOpen (tripleOverlapElement e f) := by
  rw [tripleOverlap_compositeDeterminant, PrimeSpectrum.basicOpen_mul]
  have hu : PrimeSpectrum.basicOpen
      (ambientBasisMatrix (ambientOverlapMatrix e)
        (ambientEquivBaseChange (ambientOverlapRing e) e)).det = ⊤ := by
    apply TopologicalSpace.Opens.ext
    apply Set.ext
    intro x
    exact iff_true_intro (Ideal.notMem_of_isUnit x.asIdeal (ambientOverlapMatrix_isUnit e))
  rw [hu, top_inf_eq]

end FLT.Mazur.GrassmannianChart
