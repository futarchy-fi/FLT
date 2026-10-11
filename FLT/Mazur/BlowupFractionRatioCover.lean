/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.BlowupFractionChartRatio
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Generator ratio opens cover the entire fraction chart

Any generating family of the center gives a unit ideal of ratios on every
fraction chart whose denominator belongs to the center. This includes the
exceptional locus and remains a cover after arbitrary ring base change.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.BlowupFractionChart

set_option backward.isDefEq.respectTransparency false

variable {A : Type*} [CommRing A] (I : Ideal A) (f : A)

/-- Division by the chart denominator is linear on the original center ideal. -/
def ratioLinear : I →ₗ[A] chart I f where
  toFun a := ratio I f a a.property
  map_add' a b := by
    apply Subtype.ext
    simp only [ratio_val, Submodule.coe_add, map_add, add_mul, Subalgebra.coe_add]
  map_smul' a b := by
    apply Subtype.ext
    simp only [ratio_val, Submodule.coe_smul, Algebra.smul_def, map_mul,
      Subalgebra.coe_mul, Subalgebra.coe_algebraMap, Algebra.algebraMap_self,
      RingHom.id_apply, mul_assoc]

/-- Dividing a linear combination of center generators gives a linear combination of ratios. -/
theorem ratio_mem_span {ι : Type*} (g : ι → A) (hg : ∀ i, g i ∈ I)
    (a : A) (ha : a ∈ Ideal.span (Set.range g)) (haI : a ∈ I) :
    ratio I f a haI ∈ Ideal.span (Set.range fun i => ratio I f (g i) (hg i)) := by
  let K := Ideal.span (Set.range fun i => ratio I f (g i) (hg i))
  have H : ∀ a ∈ Ideal.span (Set.range g), ∀ haI : a ∈ I, ratio I f a haI ∈ K := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨i, rfl⟩ := ha
      exact fun _ => Ideal.subset_span (Set.mem_range_self i)
    | zero =>
      intro h
      change ratioLinear I f 0 ∈ K
      rw [map_zero]
      exact K.zero_mem
    | add a b ha hb ih ih' =>
      have haI : a ∈ I := (Ideal.span_le.mpr (Set.range_subset_iff.mpr hg)) ha
      have hbI : b ∈ I := (Ideal.span_le.mpr (Set.range_subset_iff.mpr hg)) hb
      intro h
      change ratioLinear I f (⟨a, haI⟩ + ⟨b, hbI⟩) ∈ K
      rw [map_add]
      exact K.add_mem (ih haI) (ih' hbI)
    | smul c a ha ih =>
      have haI : a ∈ I := (Ideal.span_le.mpr (Set.range_subset_iff.mpr hg)) ha
      intro h
      change ratioLinear I f (c • ⟨a, haI⟩) ∈ K
      rw [map_smul]
      rw [Algebra.smul_def]
      exact K.mul_mem_left (algebraMap A _ c) (ih haI)
  exact H a ha haI

/-- Ratios of a generating family generate the unit ideal on the complete fraction chart. -/
theorem ratio_span_eq_top {ι : Type*} (g : ι → A) (hg : ∀ i, g i ∈ I)
    (hspan : Ideal.span (Set.range g) = I) (hf : f ∈ I) :
    Ideal.span (Set.range fun i => ratio I f (g i) (hg i)) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have h := ratio_mem_span I f g hg f (hspan.symm ▸ hf) hf
  rwa [ratio_self] at h

/-- The actual ratio principal opens cover, including every exceptional point. -/
theorem ratio_basicOpen_cover {ι : Type*} (g : ι → A) (hg : ∀ i, g i ∈ I)
    (hspan : Ideal.span (Set.range g) = I) (hf : f ∈ I) :
    (⨆ i, PrimeSpectrum.basicOpen (ratio I f (g i) (hg i))) = ⊤ :=
  PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr (ratio_span_eq_top I f g hg hspan hf)

/-- The same ratio opens cover after any change of coefficient ring. -/
theorem mapped_ratio_span_eq_top {ι : Type*} (g : ι → A) (hg : ∀ i, g i ∈ I)
    (hspan : Ideal.span (Set.range g) = I) (hf : f ∈ I)
    {B : Type*} [CommRing B] (ψ : chart I f →+* B) :
    Ideal.span (Set.range fun i => ψ (ratio I f (g i) (hg i))) = ⊤ := by
  rw [Set.range_comp', ← Ideal.map_span,
    ratio_span_eq_top I f g hg hspan hf, Ideal.map_top]

end FLT.Mazur.BlowupFractionChart
