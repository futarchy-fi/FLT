/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartGeneratorMap

/-!
# Imposing a prescribed polynomial basis

For a list of ambient polynomials, quotient the coefficient ring by the coordinates
of their differences from the distinguished basis. These are actual closed equations.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.HilbertChart

universe u v

variable (R : Type u) [CommRing R] (I : Type v) (d : ℕ)
variable (w : Fin d → MvPolynomial I R)

/-- The coordinate equations saying that the prescribed polynomials are the basis. -/
def basisEquation (i k : Fin d) : Coefficients R I d :=
  (basis R I d).repr (evaluation R I d (w i)) k - if i = k then 1 else 0

/-- The actual ideal of all prescribed-basis equations. -/
def basisIdeal : Ideal (Coefficients R I d) :=
  Ideal.span (Set.range fun p : Fin d × Fin d ↦ basisEquation R I d w p.1 p.2)

/-- The coordinate ring of the chart for the specified polynomial basis. -/
abbrev ChartRing := Coefficients R I d ⧸ basisIdeal R I d w

/-- The coordinate map from the ring-law parameter space to the basis chart. -/
def chartMap : Coefficients R I d →+* ChartRing R I d w :=
  Ideal.Quotient.mk _

/-- Each prescribed-basis equation vanishes in the chart ring. -/
theorem basisEquation_zero (i k : Fin d) :
    chartMap R I d w (basisEquation R I d w i k) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨(i, k), rfl⟩)

/-- The prescribed polynomial vectors become the standard coordinate vectors. -/
theorem chartMap_evaluation_repr (i k : Fin d) :
    chartMap R I d w ((basis R I d).repr (evaluation R I d (w i)) k) =
      if i = k then 1 else 0 := by
  have h := basisEquation_zero R I d w i k
  split_ifs with hik <;>
    simpa only [basisEquation, hik, ite_true, ite_false, map_sub, map_one, map_zero,
      sub_eq_zero] using h

variable {S : Type*} [CommRing S]

/-- A coefficient map kills the basis ideal exactly when its vectors satisfy the equations. -/
theorem basisIdeal_le_ker_iff (f : Coefficients R I d →+* S) :
    basisIdeal R I d w ≤ RingHom.ker f ↔
      ∀ i k, f ((basis R I d).repr (evaluation R I d (w i)) k) =
        if i = k then 1 else 0 := by
  rw [basisIdeal, Ideal.span_le]
  constructor
  · intro h i k
    have hz : f (basisEquation R I d w i k) = 0 := h ⟨(i, k), rfl⟩
    split_ifs with hik <;>
      simpa only [basisEquation, hik, ite_true, ite_false, map_sub, map_one, map_zero,
        sub_eq_zero] using hz
  · intro h x hx
    obtain ⟨⟨i, k⟩, rfl⟩ := hx
    change f (basisEquation R I d w i k) = 0
    unfold basisEquation
    rw [map_sub, h]
    split_ifs <;> simp only [map_one, map_zero, sub_self]

end FLT.Mazur.HilbertChart
