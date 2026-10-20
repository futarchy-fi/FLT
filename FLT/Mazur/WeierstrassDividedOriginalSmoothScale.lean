/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationCenterSmooth
public import FLT.Mazur.WeierstrassDilatationMorphism

/-!
# An originally smooth divided input forces the scale to be invertible

When the scale vanishes, both original coordinates of a divided input vanish
and its contraction is singular. Thus every affine overlap of a divided
chart with the original smooth open inverts the scale. This supplies the
ordinary secant denominator needed to compare the two multiplication domains.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
local notation "H" => Coordinate W s b3 b4 b6
local notation "orig" => fromOriginal W s b3 b4 b6 h3 h4 h6

/-- An originally smooth contraction cannot lie over a prime containing the scale. -/
theorem dividedOriginalSmooth_scale_notMem (p : Spec (.of H))
    (hp : toCurve W s b3 b4 b6 h3 h4 h6 p ∈
      WeierstrassIntegralChart.integralSmoothOpen W) : algebraMap R H s ∉ p.asIdeal := by
  let z := Spec.map (CommRingCat.ofHom (orig).toRingHom) p
  have hz : z ∈ (WeierstrassIntegralChart.integralCurveChart W 2) ⁻¹ᵁ
      WeierstrassIntegralChart.integralSmoothOpen W := hp
  rw [WeierstrassIntegralChart.integralCurveChart_preimage_smooth] at hz
  intro hs
  rcases WeierstrassIntegralChart.smooth_avoids_modification_generators W s b3 b4 h3 h4 z hz
      with hs' | hx | hy
  · apply hs'
    change orig (algebraMap R _ s) ∈ p.asIdeal
    rwa [AlgHom.commutes]
  · apply hx
    change orig (WeierstrassIntegralChart.coord W 2 0) ∈ p.asIdeal
    rw [fromOriginal_x]
    exact p.asIdeal.mul_mem_right _ hs
  · apply hy
    change orig (WeierstrassIntegralChart.coord W 2 1) ∈ p.asIdeal
    rw [fromOriginal_y]
    exact p.asIdeal.mul_mem_right _ hs

/-- On any affine refinement with originally smooth input the original scale is an actual unit. -/
theorem dividedOriginalSmooth_scale_isUnit {B : Type u} [CommRing B] [Algebra R B]
    (a : H →ₐ[R] B)
    (ha : Set.range (Spec.map (CommRingCat.ofHom a.toRingHom) ≫
      toCurve W s b3 b4 b6 h3 h4 h6) ⊆ WeierstrassIntegralChart.integralSmoothOpen W) :
    IsUnit (algebraMap R B s) := by
  by_contra hn
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (Ideal.span {algebraMap R B s})
    (fun h => hn (Ideal.span_singleton_eq_top.mp h))
  let p : PrimeSpectrum B := ⟨m, hm.isPrime⟩
  have h := dividedOriginalSmooth_scale_notMem W s b3 b4 b6 h3 h4 h6
    (Spec.map (CommRingCat.ofHom a.toRingHom) p) (ha ⟨p, rfl⟩)
  apply h
  change a (algebraMap R H s) ∈ m
  rw [AlgHom.commutes]
  exact hle (Ideal.subset_span (Set.mem_singleton _))

/-- Distinct divided abscissae give an ordinary secant denominator on a smooth overlap. -/
theorem dividedOriginalSmooth_originalDifference_isUnit {B : Type u} [CommRing B] [Algebra R B]
    (a c : H →ₐ[R] B)
    (ha : Set.range (Spec.map (CommRingCat.ofHom a.toRingHom) ≫
      toCurve W s b3 b4 b6 h3 h4 h6) ⊆ WeierstrassIntegralChart.integralSmoothOpen W)
    (hu : IsUnit (a (x W s b3 b4 b6) - c (x W s b3 b4 b6))) :
    IsUnit ((a.comp orig) (WeierstrassIntegralChart.coord W 2 0) -
      (c.comp orig) (WeierstrassIntegralChart.coord W 2 0)) := by
  simp only [AlgHom.comp_apply, fromOriginal_x, map_mul, AlgHom.commutes, ← mul_sub]
  exact (dividedOriginalSmooth_scale_isUnit W s b3 b4 b6 h3 h4 h6 a ha).mul hu

end FLT.Mazur.WeierstrassDilatation
