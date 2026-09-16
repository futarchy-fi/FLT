/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import FLT.Odlyzko.PoitouKernel
public import Mathlib.Analysis.Complex.Hadamard

/-!
# Zero-side positivity off the critical line

Poitou's unconditional argument first proves nonnegativity on both boundaries of the
critical strip from the Fourier transform of the numerator `f = F * cosh(x / 2)`.  The
Hadamard three-lines theorem, applied to `exp (-phi)`, then propagates that sign through
the strip.  This is the GRH-free step; Fourier positivity of `F` itself is not used.
-/

@[expose] public section

open Set
open scoped ComplexConjugate FourierTransform

namespace Odlyzko

/-- Boundary nonnegativity propagates through the closed critical strip. -/
theorem re_nonneg_on_verticalClosedStrip
    (phi : ℂ → ℂ) {z : ℂ}
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1)
    (hregular : DiffContOnCl ℂ phi (Complex.HadamardThreeLines.verticalStrip 0 1))
    (hbounded : BddAbove
      ((norm ∘ fun w ↦ Complex.exp (-phi w)) ''
        Complex.HadamardThreeLines.verticalClosedStrip 0 1))
    (hleft : ∀ w : ℂ, w.re = 0 → 0 ≤ (phi w).re)
    (hright : ∀ w : ℂ, w.re = 1 → 0 ≤ (phi w).re) :
    0 ≤ (phi z).re := by
  have hexp_regular :
      DiffContOnCl ℂ (fun w ↦ Complex.exp (-phi w))
        (Complex.HadamardThreeLines.verticalStrip 0 1) := by
    constructor
    · exact hregular.differentiableOn.neg.cexp
    · exact hregular.continuousOn.neg.cexp
  have hleft' : ∀ w ∈ Complex.re ⁻¹' ({0} : Set ℝ),
      ‖Complex.exp (-phi w)‖ ≤ (1 : ℝ) := by
    intro w hw
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    simpa using hleft w hw
  have hright' : ∀ w ∈ Complex.re ⁻¹' ({1} : Set ℝ),
      ‖Complex.exp (-phi w)‖ ≤ (1 : ℝ) := by
    intro w hw
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    simpa using hright w hw
  have hnorm := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'
    (fun w ↦ Complex.exp (-phi w)) hz hexp_regular hbounded hleft' hright'
  rw [Real.one_rpow, Real.one_rpow, one_mul, Complex.norm_exp,
    Real.exp_le_one_iff] at hnorm
  simpa using hnorm

/-- Boundedness of `phi` supplies the boundedness needed for `exp (-phi)`. -/
theorem exp_neg_bddAbove_of_bddAbove
    (phi : ℂ → ℂ)
    (hbounded : BddAbove
      ((norm ∘ phi) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1)) :
    BddAbove
      ((norm ∘ fun w ↦ Complex.exp (-phi w)) ''
        Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
  rcases hbounded with ⟨C, hC⟩
  refine ⟨Real.exp C, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  simp only [Function.comp_apply, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  calc
    (-phi w).re = -(phi w).re := by simp
    _ ≤ ‖phi w‖ := (neg_le_abs _).trans (Complex.abs_re_le_norm _)
    _ ≤ C := hC ⟨w, hw, rfl⟩

/-- Boundary positivity propagates to every point of the closed critical strip. -/
theorem PoitouBoundaryIdentification.re_nonneg
    (phi : ℂ → ℂ) (f : ℝ → ℝ) {z : ℂ}
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1)
    (hboundary : PoitouBoundaryIdentification phi f)
    (hfourier : ∀ t, 0 ≤ (𝓕 (complexify f) t).re)
    (hregular : DiffContOnCl ℂ phi (Complex.HadamardThreeLines.verticalStrip 0 1))
    (hbounded : BddAbove
      ((norm ∘ phi) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1)) :
    0 ≤ (phi z).re := by
  apply re_nonneg_on_verticalClosedStrip phi hz hregular
    (exp_neg_bddAbove_of_bddAbove phi hbounded)
  · intro w hw
    have hw' : w = w.im * Complex.I := by
      apply Complex.ext <;> simp [hw]
    rw [hw']
    exact hboundary.lower_nonneg hfourier _
  · intro w hw
    have hw' : w = 1 + w.im * Complex.I := by
      apply Complex.ext <;> simp [hw]
    rw [hw']
    exact hboundary.upper_nonneg hfourier _

/-- The functional-equation partner `1 - conj(rho)`. -/
def functionalEquationPartner (rho : ℂ) : ℂ := 1 - conj rho

@[simp] theorem functionalEquationPartner_re (rho : ℂ) :
    (functionalEquationPartner rho).re = 1 - rho.re := by
  simp [functionalEquationPartner]

@[simp] theorem functionalEquationPartner_im (rho : ℂ) :
    (functionalEquationPartner rho).im = rho.im := by
  simp [functionalEquationPartner]

/-- The functional-equation partner of a point in the critical strip remains in it. -/
theorem functionalEquationPartner_mem_verticalClosedStrip {rho : ℂ}
    (hrho : rho ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1) :
    functionalEquationPartner rho ∈
      Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
  change 0 ≤ (functionalEquationPartner rho).re ∧
    (functionalEquationPartner rho).re ≤ 1
  simp only [functionalEquationPartner_re]
  constructor <;> linarith [hrho.1, hrho.2]

/--
The corrected P4 theorem: Fourier positivity of the Poitou numerator, the exact boundary
identification, and standard analytic control imply nonnegativity of the paired zero
contribution everywhere in the critical strip, without GRH.
-/
theorem functionalEquationPair_re_nonneg
    (phi : ℂ → ℂ) (f : ℝ → ℝ) {rho : ℂ}
    (hrho : rho ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1)
    (hboundary : PoitouBoundaryIdentification phi f)
    (hfourier : ∀ t, 0 ≤ (𝓕 (complexify f) t).re)
    (hregular : DiffContOnCl ℂ phi (Complex.HadamardThreeLines.verticalStrip 0 1))
    (hbounded : BddAbove
      ((norm ∘ phi) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1)) :
    0 ≤ (phi rho + phi (functionalEquationPartner rho)).re := by
  rw [Complex.add_re]
  exact add_nonneg
    (hboundary.re_nonneg phi f hrho hfourier hregular hbounded)
    (hboundary.re_nonneg phi f
      (functionalEquationPartner_mem_verticalClosedStrip hrho) hfourier hregular hbounded)

end Odlyzko
