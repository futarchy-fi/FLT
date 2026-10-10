/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.BlowupFractionChartRatio

/-!
# Uniqueness of fraction-chart maps over the original ring

A map out of the fraction chart is determined by the original coordinate
functions whenever its denominator stays regular in the target. Regularity
persists on every localization of the chart, including exceptional ratio opens.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.BlowupFractionChart

set_option backward.isDefEq.respectTransparency false

variable {A : Type*} [CommRing A] (I : Ideal A) (f : A)

/-- Original denominators remain regular after any further chart localization. -/
theorem localized_denominator_regular (M : Submonoid (chart I f))
    (S : Type*) [CommRing S] [Algebra (chart I f) S] [IsLocalization M S] :
    IsRegular (algebraMap (chart I f) S (denominator I f)) := by
  apply isRegular_iff_mem_nonZeroDivisors.mpr
  exact IsLocalization.nonZeroDivisors_le_comap (M := M) (S := S)
    (isRegular_iff_mem_nonZeroDivisors.mp (denominator_regular I f))

/-- Maps out of a fraction chart agree if they agree on the original ring
and the common denominator is regular in the target. -/
theorem ringHom_ext_of_denominator_regular {S : Type*} [CommRing S]
    (g h : chart I f →+* S)
    (he : g.comp (algebraMap A _) = h.comp (algebraMap A _))
    (hr : IsRegular (g (denominator I f))) : g = h := by
  have hbase (a : A) : g (algebraMap A _ a) = h (algebraMap A _ a) :=
    RingHom.congr_fun he a
  have hratio (a : A) (ha : a ∈ I) : g (ratio I f a ha) = h (ratio I f a ha) := by
    apply hr.left
    dsimp only
    rw [← map_mul, denominator_mul_ratio, hbase, show g (denominator I f) =
      h (denominator I f) from hbase f, ← map_mul, denominator_mul_ratio]
  apply RingHom.ext
  intro z
  have hz : (z : Localization.Away f) ∈ Algebra.adjoin A
      ((fun a : A => algebraMap A (Localization.Away f) a *
        IsLocalization.Away.invSelf f) '' (I : Set A)) := by
    rw [← chart_eq_adjoin]
    exact z.property
  have H (y : Localization.Away f) (hy : y ∈ Algebra.adjoin A
      ((fun a : A => algebraMap A (Localization.Away f) a *
        IsLocalization.Away.invSelf f) '' (I : Set A))) :
      ∀ hy' : y ∈ chart I f, g ⟨y, hy'⟩ = h ⟨y, hy'⟩ := by
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      exact fun _ => hratio a ha
    | algebraMap a => exact fun _ => hbase a
    | add x y hx hy ih ih' =>
      intro hxy
      have hx' : x ∈ chart I f := by rwa [chart_eq_adjoin]
      have hy' : y ∈ chart I f := by rwa [chart_eq_adjoin]
      exact (map_add g ⟨x, hx'⟩ ⟨y, hy'⟩).trans
        ((congrArg₂ (· + ·) (ih hx') (ih' hy')).trans (map_add h _ _).symm)
    | mul x y hx hy ih ih' =>
      intro hxy
      have hx' : x ∈ chart I f := by rwa [chart_eq_adjoin]
      have hy' : y ∈ chart I f := by rwa [chart_eq_adjoin]
      exact (map_mul g ⟨x, hx'⟩ ⟨y, hy'⟩).trans
        ((congrArg₂ (· * ·) (ih hx') (ih' hy')).trans (map_mul h _ _).symm)
  exact H z hz z.property

end FLT.Mazur.BlowupFractionChart
