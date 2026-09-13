/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import FLT.Odlyzko.Discard
public import FLT.Odlyzko.PoitouKernel

/-!
# Poitou regularization

Poitou's unconditional test class is weaker at infinity than the admissible class used by
the current explicit-formula interface.  The theorem below isolates the regularization
step: prove the discard inequality for admissible approximants and pass its real lower
bound to the limit.  No limiting identity is hidden in the interface.
-/

@[expose] public section

open MeasureTheory Filter
open scoped FourierTransform Topology

namespace Odlyzko

open Module NumberField

/-- The difference quotient in Poitou's weak unconditional test class. -/
noncomputable def poitouDiffQuot (f : ℝ → ℝ) : ℝ → ℂ :=
  fun x ↦ (((f 0 - f x) / x : ℝ) : ℂ)

/--
The weak test-function conditions in Poitou's unconditional Proposition 5.

Unlike `IsAdmissibleTestFn`, this structure does not demand an exponentially weighted
integrability margin.  That gap is crossed by `PoitouRegularization` below.
-/
structure IsPoitouTestFn (f : ℝ → ℝ) : Prop where
  even : Function.Even f
  zero : f 0 = 1
  nonneg : ∀ x, 0 ≤ f x
  integrable : IntegrableOn f (Set.Ici 0)
  kernel_bv : BoundedVariationOn (poitouKernel f) (Set.Ici 0)
  diffQuot_bv : BoundedVariationOn (poitouDiffQuot f) (Set.Ici 0)
  kernel_jump_avg : ∀ x : ℝ, ∃ L R : ℂ,
    Filter.Tendsto (poitouKernel f) (nhdsWithin x (Set.Iio x)) (nhds L)
    ∧ Filter.Tendsto (poitouKernel f) (nhdsWithin x (Set.Ioi x)) (nhds R)
    ∧ poitouKernel f x = (L + R) / 2
  fourier_nonneg : ∀ t, 0 ≤ (𝓕 (complexify f) t).re

/--
Admissible approximants converging pointwise to the corrected Poitou kernel.

The separate convergence of explicit-formula terms remains visible in the theorem that
uses this structure; pointwise convergence alone cannot justify exchanging every sum and
integral in that formula.
-/
structure PoitouRegularization (f : ℝ → ℝ) where
  weak : IsPoitouTestFn f
  /-- Strong test functions to which the existing explicit-formula interface applies. -/
  approximant : ℕ → ℝ → ℂ
  admissible : ∀ n, DedekindResidue.IsAdmissibleTestFn (approximant n)
  tendsto_kernel : ∀ x,
    Tendsto (fun n ↦ approximant n x) atTop (nhds (poitouKernel f x))

/-- An upper bound survives passage to a convergent sequential regularization. -/
theorem le_of_tendsto_of_forall_le {u : ℕ → ℝ} {a b : ℝ}
    (hu : Tendsto u atTop (nhds a)) (hub : ∀ n, u n ≤ b) : a ≤ b := by
  exact isClosed_Iic.mem_of_tendsto hu (Filter.Eventually.of_forall hub)

/--
The regularized discard inequality.  Every approximant is covered by the strong
explicit-formula interface; convergence of the complete real lower side then gives the
same inequality for the weak Poitou limit.
-/
theorem log_discriminant_ge_of_poitouRegularization
    (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    (f : ℝ → ℝ) (regularization : PoitouRegularization f)
    (phi : ℕ → ℂ → ℂ) (zeroSide archimedeanIntegral primeSide : ℕ → ℂ)
    (hformula : ∀ n, TotallyComplexExplicitFormula K (regularization.approximant n)
      (phi n) (zeroSide n) (archimedeanIntegral n) (primeSide n))
    (hF0 : ∀ n, regularization.approximant n 0 = 1)
    (hzero : ∀ n, 0 ≤ (zeroSide n).re) (hprime : ∀ n, 0 ≤ (primeSide n).re)
    (limit : ℝ)
    (hlimit : Tendsto
      (fun n ↦ (finrank ℚ K : ℝ) * archimedeanLowerTerm (archimedeanIntegral n) -
        (phi n 0 + phi n 1).re)
      atTop (nhds limit)) :
    limit ≤ Real.log |(discr K : ℝ)| := by
  apply le_of_tendsto_of_forall_le hlimit
  intro n
  exact discriminant_log_ge_archimedean_sub_poles K
    (regularization.approximant n) (phi n) (zeroSide n)
    (archimedeanIntegral n) (primeSide n) (hformula n) (hF0 n) (hzero n) (hprime n)

end Odlyzko
