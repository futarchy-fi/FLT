/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFractionEquation

/-!
# The actual x-direction fraction map

The original fractions s/x and y/x give a map from the actual x-direction
algebra. Its contraction is the original coordinate map, and conversely it
recovers every x-chart map after the original horizontal coordinate is inverted.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassModificationX

set_option backward.isDefEq.respectTransparency false

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
  (f : WeierstrassIntegralChart.Coordinate W 2 →ₐ[R] S)
  (d : S) (hd : f (WeierstrassIntegralChart.coord W 2 0) * d = 1)

/-- The actual x-chart map given by the original fractions s/x and y/x. -/
def fractionMap : Coordinate W s b3 b4 b6 →ₐ[R] S :=
  evaluation W s b3 b4 b6 (d * algebraMap R S s)
    (d * f (WeierstrassIntegralChart.coord W 2 1))
    (fraction_incidence W s b3 b4 b6 h3 h4 h6 f d hd)

/-- The incidence coordinate is the original scale divided by the original horizontal. -/
@[simp] theorem fractionMap_t :
    fractionMap W s b3 b4 b6 h3 h4 h6 f d hd (t W s b3 b4 b6) =
      d * algebraMap R S s := evaluation_t _ _ _ _ _ _ _ _

/-- The slope coordinate is the ratio of the actual original coordinates. -/
@[simp] theorem fractionMap_v :
    fractionMap W s b3 b4 b6 h3 h4 h6 f d hd (v W s b3 b4 b6) =
      d * f (WeierstrassIntegralChart.coord W 2 1) := evaluation_v _ _ _ _ _ _ _ _

/-- The divided cubic recovers the actual original horizontal coordinate. -/
@[simp] theorem fractionMap_x :
    fractionMap W s b3 b4 b6 h3 h4 h6 f d hd (x W s b3 b4 b6) =
      f (WeierstrassIntegralChart.coord W 2 0) := by
  simp only [x, map_add, map_sub, map_mul, map_pow, AlgHom.commutes,
    fractionMap_t, fractionMap_v]
  exact (fraction_horizontal W s b3 b4 b6 h3 h4 h6 f d hd).symm

/-- The retained vertical coordinate is also the actual original coordinate. -/
@[simp] theorem fractionMap_y :
    fractionMap W s b3 b4 b6 h3 h4 h6 f d hd (y W s b3 b4 b6) =
      f (WeierstrassIntegralChart.coord W 2 1) := by
  rw [y, map_mul, fractionMap_x, fractionMap_v, ← mul_assoc, hd, one_mul]

/-- The fraction map preserves the original contraction on every function. -/
theorem fractionMap_fromOriginal :
    (fractionMap W s b3 b4 b6 h3 h4 h6 f d hd).comp
      (fromOriginal W s b3 b4 b6 h3 h4 h6) = f := by
  apply WeierstrassIntegralChart.hom_ext
  intro i
  fin_cases i <;> simp [WeierstrassIntegralChart.coord_self]

/-- Every actual x-chart map is recovered from its original fractions. -/
theorem fractionMap_comp_contraction (g : Coordinate W s b3 b4 b6 →ₐ[R] S)
    (hg : g (x W s b3 b4 b6) * d = 1) :
    fractionMap W s b3 b4 b6 h3 h4 h6
      (g.comp (fromOriginal W s b3 b4 b6 h3 h4 h6)) d (by simpa using hg) = g := by
  apply hom_ext
  · rw [fractionMap_t]
    have he := congrArg g (incidence W s b3 b4 b6)
    simp only [map_mul, AlgHom.commutes] at he
    linear_combination -d * he + g (t W s b3 b4 b6) * hg
  · rw [fractionMap_v, AlgHom.comp_apply, fromOriginal_y, y, map_mul]
    calc
      d * (g (x W s b3 b4 b6) * g (v W s b3 b4 b6)) =
          (g (x W s b3 b4 b6) * d) * g (v W s b3 b4 b6) := by ring
      _ = g (v W s b3 b4 b6) := by rw [hg, one_mul]

/-- A regular original horizontal image makes the actual lift unique. -/
theorem lift_unique (g k : Coordinate W s b3 b4 b6 →ₐ[R] S)
    (hx : IsRegular (g (x W s b3 b4 b6)))
    (he : g.comp (fromOriginal W s b3 b4 b6 h3 h4 h6) =
      k.comp (fromOriginal W s b3 b4 b6 h3 h4 h6)) : g = k := by
  have hh : g (x W s b3 b4 b6) = k (x W s b3 b4 b6) := by
    simpa only [AlgHom.comp_apply, fromOriginal_x] using
      congrArg (fun q => q (WeierstrassIntegralChart.coord W 2 0)) he
  apply hom_ext
  · apply hx.right
    have hg := congrArg g (incidence W s b3 b4 b6)
    have hk := congrArg k (incidence W s b3 b4 b6)
    simp only [map_mul, AlgHom.commutes] at hg hk
    dsimp only
    rw [hg, hh, hk]
  · apply hx.left
    have hv : g (y W s b3 b4 b6) = k (y W s b3 b4 b6) := by
      simpa only [AlgHom.comp_apply, fromOriginal_y] using
        congrArg (fun q => q (WeierstrassIntegralChart.coord W 2 1)) he
    simpa only [y, map_mul, ← hh] using hv

end FLT.Mazur.WeierstrassModificationX
