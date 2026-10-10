/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationReesYAtlas

/-!
# The actual vertical fraction ratios cover their chart

The original ratios s/y and x/y generate the unit ideal in the vertical
fraction algebra. Their principal spectra therefore cover it, and determine
the vertical map into the fraction atlas uniquely by its two transitions.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassModificationReesCoordinates

universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) (hs : s ≠ 0)

include h3 h4 h6 hs

/-- The two original ratios generate the unit ideal in the vertical fraction algebra. -/
theorem vertical_ratios_coprime : IsCoprime (verticalScale W s) (verticalHorizontal W s) := by
  have h := (WeierstrassModificationY.ratios_coprime W s b3 b4 b6).map
    (WeierstrassModificationY.verticalReesChartEquiv W s b3 b4 b6 h3 h4 h6 hs).toRingHom
  simpa only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_ringEquiv,
    verticalEquiv_r, verticalEquiv_u] using h

/-- Every vertical fraction prime avoids one of the two original ratios. -/
theorem vertical_ratio_exists_not_mem
    (p : PrimeSpectrum (WeierstrassModificationY.verticalReesChart W s)) :
    ∃ i : Fin 2, ![verticalScale W s, verticalHorizontal W s] i ∉ p.asIdeal := by
  obtain ⟨a, b, hab⟩ := vertical_ratios_coprime W s b3 b4 b6 h3 h4 h6 hs
  by_contra h
  push Not at h
  have h0 := p.asIdeal.mul_mem_left a (h 0)
  have h1 := p.asIdeal.mul_mem_left b (h 1)
  exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem p.asIdeal
    (by simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, hab] using
      p.asIdeal.add_mem h0 h1) isUnit_one)

/-- The two actual fraction ratio localizations cover the entire vertical spectrum. -/
def verticalRatioCover :
    (Spec (.of (WeierstrassModificationY.verticalReesChart W s))).OpenCover where
  I₀ := Fin 2
  X i := Spec (.of (Localization.Away (![verticalScale W s, verticalHorizontal W s] i)))
  f i := PrincipalAffineRefinement.inclusion (![verticalScale W s, verticalHorizontal W s] i)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, fun _ => inferInstance⟩
    intro p
    obtain ⟨i, hi⟩ := vertical_ratio_exists_not_mem W s b3 b4 b6 h3 h4 h6 hs p
    refine ⟨i, ?_⟩
    rw [PrincipalAffineRefinement.range_inclusion]
    exact hi

/-- The actual two fraction transitions determine the entire vertical atlas map. -/
theorem verticalChart_unique
    (g : Spec (.of (WeierstrassModificationY.verticalReesChart W s)) ⟶
      fractionAtlas W s b3 b4 b6 h3 h4 h6 hs)
    (h0 : verticalScaleInclusion W s ≫ g =
      verticalToScale W s b3 b4 b6 h3 h4 h6 hs ≫ scaleChart W s b3 b4 b6 h3 h4 h6 hs)
    (h1 : verticalHorizontalInclusion W s ≫ g =
      verticalToHorizontal W s b3 b4 b6 h3 h4 h6 hs ≫
        horizontalChart W s b3 b4 b6 h3 h4 h6 hs) :
    g = verticalChart W s b3 b4 b6 h3 h4 h6 hs := by
  apply (verticalRatioCover W s b3 b4 b6 h3 h4 h6 hs).hom_ext
  intro i
  change Fin 2 at i
  fin_cases i
  · change verticalScaleInclusion W s ≫ g =
      verticalScaleInclusion W s ≫ verticalChart W s b3 b4 b6 h3 h4 h6 hs
    rw [h0, verticalChart_scale]
  · change verticalHorizontalInclusion W s ≫ g =
      verticalHorizontalInclusion W s ≫ verticalChart W s b3 b4 b6 h3 h4 h6 hs
    rw [h1, verticalChart_horizontal]

end FLT.Mazur.WeierstrassModificationReesCoordinates
