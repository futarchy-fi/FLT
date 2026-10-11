/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.BlowupFractionChartRatio
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Principalization and regularity on base-changed fraction charts

The full original center becomes the denominator ideal on its fraction chart.
This equality survives every scalar extension. Regularity is asserted only
for flat extensions, and for subsequent localizations, not arbitrary changes
of coefficients.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.BlowupFractionChart

set_option backward.isDefEq.respectTransparency false

variable {A : Type*} [CommRing A] (I : Ideal A) (f : A)

/-- The entire original ideal becomes the principal denominator ideal on the fraction chart. -/
theorem center_map_eq_denominator (hf : f ∈ I) :
    I.map (algebraMap A (chart I f)) = Ideal.span {denominator I f} := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    exact Ideal.mem_span_singleton.mpr ⟨ratio I f a ha, (denominator_mul_ratio I f a ha).symm⟩
  · apply Ideal.span_le.mpr
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact Ideal.mem_map_of_mem _ hf

/-- Principalization persists under an arbitrary map out of the fraction chart. -/
theorem center_map_eq_mapped_denominator (hf : f ∈ I)
    {B : Type*} [CommRing B] (ψ : chart I f →+* B) :
    I.map (ψ.comp (algebraMap A (chart I f))) = Ideal.span {ψ (denominator I f)} := by
  rw [← Ideal.map_map, center_map_eq_denominator I f hf, Ideal.map_span, Set.image_singleton]

/-- A regular element of the coefficient ring stays regular under a flat extension. -/
theorem regular_algebraMap_of_flat {B : Type*} [CommRing B] [Algebra A B]
    [Module.Flat A B] (a : A) (ha : IsRegular a) :
    IsRegular (algebraMap A B a) := by
  have h := Module.Flat.isSMulRegular_of_isRegular (M := B) ha
  have hl : IsLeftRegular (algebraMap A B a) := by
    intro x y he
    apply h
    simpa only [Algebra.smul_def] using he
  exact ⟨hl, fun x y he => hl (by simpa only [mul_comm] using he)⟩

/-- Flat change of the fraction chart retains its original denominator as a nonzerodivisor. -/
theorem flat_denominator_regular {B : Type*} [CommRing B] [Algebra (chart I f) B]
    [Module.Flat (chart I f) B] :
    IsRegular (algebraMap (chart I f) B (denominator I f)) :=
  regular_algebraMap_of_flat _ (denominator_regular I f)

end FLT.Mazur.BlowupFractionChart
