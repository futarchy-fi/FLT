/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationMorphism
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Dividing the original coordinates in an arbitrary algebra

An inverse to the original scale gives an actual divided-chart map. Both
composites retain the original contraction, so this applies to principal
localizations as well as coefficient extensions.
-/

@[expose] public noncomputable section

open WeierstrassCurve

namespace FLT.Mazur.WeierstrassDilatation

set_option backward.isDefEq.respectTransparency false

universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
  (f : WeierstrassIntegralChart.Coordinate W 2 →ₐ[R] S)
  (d : S) (hd : algebraMap R S s * d = 1)

include h3 h4 h6 hd in
/-- Dividing the actual original coordinates solves the divided equation. -/
theorem fraction_equation :
    (d * f (WeierstrassIntegralChart.coord W 2 1)) ^ 2 +
        (algebraMap R S W.a₁ * (d * f (WeierstrassIntegralChart.coord W 2 0)) +
          algebraMap R S b3) * (d * f (WeierstrassIntegralChart.coord W 2 1)) =
      algebraMap R S s * (d * f (WeierstrassIntegralChart.coord W 2 0)) ^ 3 +
        algebraMap R S W.a₂ * (d * f (WeierstrassIntegralChart.coord W 2 0)) ^ 2 +
        algebraMap R S b4 * (d * f (WeierstrassIntegralChart.coord W 2 0)) +
        algebraMap R S b6 := by
  apply equation_of_scaled W s b3 b4 b6 h3 h4 h6
    (isUnit_iff_exists_inv.mpr ⟨d, hd⟩).isRegular
  have he := WeierstrassIntegralChart.coord_equation W 2
  rw [Projective.equation_iff] at he ⊢
  have hm := congrArg f he
  simp only [map_sub, map_zero, map_add, map_mul, map_pow, AlgHom.commutes,
    WeierstrassIntegralChart.coord_self, map_one, map_a₁, map_a₂, map_a₃,
    map_a₄, map_a₆] at hm
  simpa only [Projective.fin3_def_ext, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆,
    ← mul_assoc, hd, one_mul] using hm

/-- The actual algebra map given by the fractions x/s and y/s. -/
def fractionMap : Coordinate W s b3 b4 b6 →ₐ[R] S :=
  evaluation W s b3 b4 b6
    (d * f (WeierstrassIntegralChart.coord W 2 0))
    (d * f (WeierstrassIntegralChart.coord W 2 1))
    (fraction_equation W s b3 b4 b6 h3 h4 h6 f d hd)

/-- The horizontal divided coordinate maps to its actual original fraction. -/
@[simp] theorem fractionMap_x :
    fractionMap W s b3 b4 b6 h3 h4 h6 f d hd (x W s b3 b4 b6) =
      d * f (WeierstrassIntegralChart.coord W 2 0) := evaluation_x _ _ _ _ _ _ _ _

/-- The vertical divided coordinate maps to its actual original fraction. -/
@[simp] theorem fractionMap_y :
    fractionMap W s b3 b4 b6 h3 h4 h6 f d hd (y W s b3 b4 b6) =
      d * f (WeierstrassIntegralChart.coord W 2 1) := evaluation_y _ _ _ _ _ _ _ _

/-- The fraction map retains the original coordinate map exactly. -/
theorem fractionMap_fromOriginal :
    (fractionMap W s b3 b4 b6 h3 h4 h6 f d hd).comp
      (fromOriginal W s b3 b4 b6 h3 h4 h6) = f := by
  apply WeierstrassIntegralChart.hom_ext
  intro i
  fin_cases i <;>
    simp [WeierstrassIntegralChart.coord_self, ← mul_assoc, hd]

/-- After any divided-chart map, taking the original fractions recovers that map. -/
theorem fractionMap_comp_contraction (g : Coordinate W s b3 b4 b6 →ₐ[R] S) :
    fractionMap W s b3 b4 b6 h3 h4 h6
      (g.comp (fromOriginal W s b3 b4 b6 h3 h4 h6)) d hd = g := by
  have hd' : d * algebraMap R S s = 1 := by rw [mul_comm, hd]
  apply hom_ext <;> simp [← mul_assoc, hd']

end FLT.Mazur.WeierstrassDilatation
