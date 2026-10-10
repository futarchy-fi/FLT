/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationYFractionEquation

/-!
# The actual y-direction fraction map

The original fractions s/y, x/y, y define the y-chart map. Contraction
recovers the original map, and regularity of y makes every lift unique.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassModificationY

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
  (f : WeierstrassIntegralChart.Coordinate W 2 →ₐ[R] S)
  (d : S) (hd : f (WeierstrassIntegralChart.coord W 2 1) * d = 1)

/-- The actual y-chart evaluation at the original fractions. -/
def fractionMap : Coordinate W s b3 b4 b6 →ₐ[R] S :=
  evaluation W s b3 b4 b6 ![d * algebraMap R S s,
    d * f (WeierstrassIntegralChart.coord W 2 0),
    f (WeierstrassIntegralChart.coord W 2 1)]
    (fraction_equation W s b3 b4 b6 h3 h4 h6 f d hd) (by
      change (d * algebraMap R S s) * f (WeierstrassIntegralChart.coord W 2 1) = _
      linear_combination algebraMap R S s * hd)

/-- The three coordinates are the original scale ratio, horizontal ratio and vertical. -/
@[simp] theorem fractionMap_coord (i : Fin 3) :
    fractionMap W s b3 b4 b6 h3 h4 h6 f d hd (coord W s b3 b4 b6 i) =
      ![d * algebraMap R S s, d * f (WeierstrassIntegralChart.coord W 2 0),
        f (WeierstrassIntegralChart.coord W 2 1)] i := evaluation_coord _ _ _ _ _ _ _ _ _

/-- The original contraction is preserved on every original function. -/
theorem fractionMap_fromOriginal :
    (fractionMap W s b3 b4 b6 h3 h4 h6 f d hd).comp
      (fromOriginal W s b3 b4 b6 h3 h4 h6) = f := by
  apply WeierstrassIntegralChart.hom_ext
  intro i
  fin_cases i
  · change fractionMap W s b3 b4 b6 h3 h4 h6 f d hd
      (fromOriginal W s b3 b4 b6 h3 h4 h6 (WeierstrassIntegralChart.coord W 2 0)) = _
    rw [fromOriginal_x, map_mul, fractionMap_coord, fractionMap_coord]
    change (d * f (WeierstrassIntegralChart.coord W 2 0)) *
      f (WeierstrassIntegralChart.coord W 2 1) = f (WeierstrassIntegralChart.coord W 2 0)
    linear_combination f (WeierstrassIntegralChart.coord W 2 0) * hd
  · simp
  · simp [WeierstrassIntegralChart.coord_self]

/-- A regular original vertical image makes the actual y-chart lift unique. -/
theorem lift_unique (g k : Coordinate W s b3 b4 b6 →ₐ[R] S)
    (hz : IsRegular (g (coord W s b3 b4 b6 2)))
    (he : g.comp (fromOriginal W s b3 b4 b6 h3 h4 h6) =
      k.comp (fromOriginal W s b3 b4 b6 h3 h4 h6)) : g = k := by
  have hh : g (coord W s b3 b4 b6 2) = k (coord W s b3 b4 b6 2) := by
    simpa only [AlgHom.comp_apply, fromOriginal_y] using
      congrArg (fun q => q (WeierstrassIntegralChart.coord W 2 1)) he
  apply hom_ext
  intro i
  fin_cases i
  · change g (coord W s b3 b4 b6 0) = k (coord W s b3 b4 b6 0)
    apply hz.right
    have hg := congrArg g (incidence W s b3 b4 b6)
    have hk := congrArg k (incidence W s b3 b4 b6)
    simp only [map_mul, AlgHom.commutes] at hg hk
    dsimp only
    rw [hg, hh, hk]
  · change g (coord W s b3 b4 b6 1) = k (coord W s b3 b4 b6 1)
    apply hz.right
    have hx := congrArg (fun q => q (WeierstrassIntegralChart.coord W 2 0)) he
    simpa only [AlgHom.comp_apply, fromOriginal_x, map_mul, ← hh] using hx
  · exact hh

/-- Every y-chart map with invertible original vertical is recovered from its fractions. -/
theorem fractionMap_comp_contraction (g : Coordinate W s b3 b4 b6 →ₐ[R] S)
    (hg : g (coord W s b3 b4 b6 2) * d = 1) :
    fractionMap W s b3 b4 b6 h3 h4 h6
      (g.comp (fromOriginal W s b3 b4 b6 h3 h4 h6)) d (by simpa using hg) = g := by
  symm
  apply lift_unique W s b3 b4 b6 h3 h4 h6 g _
    (isUnit_iff_exists_inv.mpr ⟨d, hg⟩).isRegular
  exact (fractionMap_fromOriginal W s b3 b4 b6 h3 h4 h6 _ _ _).symm

end FLT.Mazur.WeierstrassModificationY
