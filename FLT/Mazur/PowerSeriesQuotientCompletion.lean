/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicCompletionPrincipal
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Completion of a polynomial hypersurface

The power-series completion of the polynomial ring and exactness for a
principal quotient identify the formal hypersurface with its completion.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PowerSeriesQuotientCompletion
variable {K σ : Type*} [Field K] [Finite σ]

/-- The formal hypersurface is the completion of its polynomial equation. -/
def equivalence (r : MvPolynomial σ K) (hr : r ≠ 0) :
    (MvPowerSeries σ K ⧸ Ideal.span {(r : MvPowerSeries σ K)}) ≃ₐ[K]
      AdicCompletion ((MvPolynomial.idealOfVars σ K).map
        (Ideal.Quotient.mk (Ideal.span {r}))) (MvPolynomial σ K ⧸ Ideal.span {r}) :=
  (Ideal.quotientEquivAlg _ _
    ((MvPowerSeries.toAdicCompletionAlgEquiv σ K).restrictScalars K) (by
      rw [Ideal.map_span, Set.image_singleton]
      congr 1
      exact congrArg (fun x ↦ ({x} : Set _)) (MvPowerSeries.toAdicCompletion_coe r).symm)).trans
    ((AdicCompletionPrincipal.equivalence (MvPolynomial.idealOfVars σ K) r
      (mul_right_injective₀ hr)).restrictScalars K)

omit [Finite σ] in
theorem idealOfVars_eq_ker : MvPolynomial.idealOfVars σ K =
    RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial σ K →+* K) := by
  ext p
  rw [← pow_one (MvPolynomial.idealOfVars σ K),
    MvPolynomial.mem_pow_idealOfVars_iff']
  simp only [RingHom.mem_ker, MvPolynomial.constantCoeff_eq]
  constructor
  · intro h
    exact h 0 (by simp)
  · intro h d hd
    have hd0 : d = 0 := by
      simpa only [Nat.lt_one_iff, Finsupp.degree_eq_zero_iff] using hd
    simpa [hd0] using h

omit [Finite σ] in
/-- A presentation compatible with evaluation maps the variable ideal onto its kernel. -/
theorem map_idealOfVars {A : Type*} [CommRing A] [Algebra K A]
    (f : MvPolynomial σ K →ₐ[K] A) (e : A →ₐ[K] K)
    (hf : Function.Surjective f)
    (he : ∀ p, e (f p) = MvPolynomial.constantCoeff p) :
    (MvPolynomial.idealOfVars σ K).map f.toRingHom = RingHom.ker e.toRingHom := by
  have h : MvPolynomial.idealOfVars σ K =
      (RingHom.ker e.toRingHom).comap f.toRingHom := by
    rw [idealOfVars_eq_ker]
    ext p
    change MvPolynomial.constantCoeff p = 0 ↔ e (f p) = 0
    rw [he]
  rw [h, Ideal.map_comap_of_surjective f.toRingHom hf]
end FLT.Mazur.PowerSeriesQuotientCompletion
