/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationMorphism

/-!
# The divided chart's actual lifting property

Over an algebra in which the scaling parameter is regular, an original
Weierstrass chart point lifts uniquely exactly when both of its coordinates
are divisible by that parameter. This characterizes the chart by the actual
contraction map, rather than an arbitrary generic isomorphism.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassDilatation

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
  (hs : IsRegular (algebraMap R S s))

include hs

/-- Regularity of the scale makes a lift through the actual contraction unique. -/
theorem lift_unique (f g : Coordinate W s b3 b4 b6 →ₐ[R] S)
    (h : f.comp (fromOriginal W s b3 b4 b6 h3 h4 h6) =
      g.comp (fromOriginal W s b3 b4 b6 h3 h4 h6)) : f = g := by
  apply hom_ext
  · apply hs.left
    simpa only [AlgHom.comp_apply, fromOriginal_x, map_mul, AlgHom.commutes] using
      congrArg (fun q => q (WeierstrassIntegralChart.coord W 2 0)) h
  · apply hs.left
    simpa only [AlgHom.comp_apply, fromOriginal_y, map_mul, AlgHom.commutes] using
      congrArg (fun q => q (WeierstrassIntegralChart.coord W 2 1)) h

/-- Divisibility of the actual original coordinates constructs a lift. -/
theorem exists_lift_of_divisible (f : WeierstrassIntegralChart.Coordinate W 2 →ₐ[R] S)
    (hu : algebraMap R S s ∣ f (WeierstrassIntegralChart.coord W 2 0))
    (hv : algebraMap R S s ∣ f (WeierstrassIntegralChart.coord W 2 1)) :
    ∃ g : Coordinate W s b3 b4 b6 →ₐ[R] S,
      g.comp (fromOriginal W s b3 b4 b6 h3 h4 h6) = f := by
  obtain ⟨u, hu⟩ := hu
  obtain ⟨v, hv⟩ := hv
  have hp : (W.map (algebraMap R S)).toProjective.Equation
      ![algebraMap R S s * u, algebraMap R S s * v, 1] := by
    convert WeierstrassIntegralChart.projective_equation_of_hom W 2 f using 1
    ext i
    fin_cases i <;> simp [hu, hv, WeierstrassIntegralChart.coord_self]
  let g := evaluation W s b3 b4 b6 u v
    (equation_of_scaled W s b3 b4 b6 h3 h4 h6 hs u v hp)
  refine ⟨g, ?_⟩
  apply WeierstrassIntegralChart.hom_ext
  intro i
  fin_cases i <;>
    simp [g, fromOriginal, WeierstrassIntegralChart.evaluation_coord,
      WeierstrassIntegralChart.coord_self, hu, hv]

/-- A unique lift exists precisely when the original coordinates are divisible by the scale. -/
theorem existsUnique_lift_iff (f : WeierstrassIntegralChart.Coordinate W 2 →ₐ[R] S) :
    (∃! g : Coordinate W s b3 b4 b6 →ₐ[R] S,
      g.comp (fromOriginal W s b3 b4 b6 h3 h4 h6) = f) ↔
        algebraMap R S s ∣ f (WeierstrassIntegralChart.coord W 2 0) ∧
        algebraMap R S s ∣ f (WeierstrassIntegralChart.coord W 2 1) := by
  constructor
  · rintro ⟨g, hg, _⟩
    rw [← hg]
    exact ⟨⟨g (x W s b3 b4 b6), by simp⟩, ⟨g (y W s b3 b4 b6), by simp⟩⟩
  · rintro ⟨hu, hv⟩
    obtain ⟨g, hg⟩ := exists_lift_of_divisible W s b3 b4 b6 h3 h4 h6 hs f hu hv
    exact ⟨g, hg, fun q hq => lift_unique W s b3 b4 b6 h3 h4 h6 hs q g (hq.trans hg.symm)⟩

end FLT.Mazur.WeierstrassDilatation
