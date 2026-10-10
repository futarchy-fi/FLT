/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationYOverlap
public import FLT.Mazur.WeierstrassModificationYMorphism
public import FLT.Mazur.WeierstrassModificationXMorphism
public import FLT.Mazur.WeierstrassDilatationMorphism

/-!
# The y-direction substitutions preserve the original contraction

Both ratio substitutions recover the same original x and y coordinates,
so their actual principal-open scheme maps will lie over the original cubic.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassModificationY

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)

/-- Inverting the scale ratio recovers the original vertical coordinate. -/
theorem mapped_scale_inverse {S : Type u} [CommRing S] [Algebra R S]
    (f : Coordinate W s b3 b4 b6 →ₐ[R] S) (a : Sˣ)
    (ha : f (coord W s b3 b4 b6 0) = a) :
    algebraMap R S s * (↑a⁻¹ : S) = f (coord W s b3 b4 b6 2) := by
  have h := congrArg f (incidence W s b3 b4 b6)
  simp only [map_mul, AlgHom.commutes, ha] at h
  rw [← h, mul_right_comm, Units.mul_inv, one_mul]

variable (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

/-- The divided substitution preserves the contraction on actual coordinate algebras. -/
theorem toDivided_fromOriginal {S : Type u} [CommRing S] [Algebra R S]
    (f : Coordinate W s b3 b4 b6 →ₐ[R] S) (a : Sˣ)
    (ha : f (coord W s b3 b4 b6 0) = a) :
    (toDivided W s b3 b4 b6 f a ha).comp
        (WeierstrassDilatation.fromOriginal W s b3 b4 b6 h3 h4 h6) =
      f.comp (fromOriginal W s b3 b4 b6 h3 h4 h6) := by
  apply WeierstrassIntegralChart.hom_ext
  intro i
  fin_cases i
  · simp only [Fin.zero_eta, AlgHom.comp_apply,
      WeierstrassDilatation.fromOriginal_x, map_mul, AlgHom.commutes, toDivided_x,
      fromOriginal_x]
    rw [mul_left_comm, mapped_scale_inverse W s b3 b4 b6 f a ha]
  · simp only [Fin.mk_one, AlgHom.comp_apply, WeierstrassDilatation.fromOriginal_y,
      map_mul, AlgHom.commutes, toDivided_y, fromOriginal_y]
    exact mapped_scale_inverse W s b3 b4 b6 f a ha
  · simp [WeierstrassIntegralChart.coord_self]

/-- The x-direction substitution also preserves the original affine contraction. -/
theorem toX_fromOriginal {S : Type u} [CommRing S] [Algebra R S]
    (f : Coordinate W s b3 b4 b6 →ₐ[R] S) (a : Sˣ)
    (ha : f (coord W s b3 b4 b6 1) = a) :
    (toX W s b3 b4 b6 f a ha).comp
        (WeierstrassModificationX.fromOriginal W s b3 b4 b6 h3 h4 h6) =
      f.comp (fromOriginal W s b3 b4 b6 h3 h4 h6) := by
  apply WeierstrassIntegralChart.hom_ext
  intro i
  fin_cases i
  · simp only [Fin.zero_eta, AlgHom.comp_apply, WeierstrassModificationX.fromOriginal_x,
      toX_x, fromOriginal_x, map_mul, ha]
    exact mul_comm _ _
  · simp only [Fin.mk_one, AlgHom.comp_apply, WeierstrassModificationX.fromOriginal_y,
      WeierstrassModificationX.y, map_mul, toX_x, toX_v, fromOriginal_y]
    rw [mul_assoc, Units.mul_inv, mul_one]
  · simp [WeierstrassIntegralChart.coord_self]

/-- The actual spectrum map to the divided chart preserves the projective contraction. -/
theorem toDivided_toCurve {S : Type u} [CommRing S] [Algebra R S]
    (f : Coordinate W s b3 b4 b6 →ₐ[R] S) (a : Sˣ)
    (ha : f (coord W s b3 b4 b6 0) = a) :
    Spec.map (CommRingCat.ofHom (toDivided W s b3 b4 b6 f a ha).toRingHom) ≫
        WeierstrassDilatation.toCurve W s b3 b4 b6 h3 h4 h6 =
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫ toCurve W s b3 b4 b6 h3 h4 h6 := by
  have hr := congrArg (fun g : WeierstrassIntegralChart.Coordinate W 2 →ₐ[R] S =>
    CommRingCat.ofHom g.toRingHom) (toDivided_fromOriginal W s b3 b4 b6 h3 h4 h6 f a ha)
  change _ ≫ (Spec.map _ ≫ _) = _ ≫ (Spec.map _ ≫ _)
  simp only [← Category.assoc, ← Spec.map_comp]
  exact congrArg (fun g => Spec.map g ≫ WeierstrassIntegralChart.integralCurveChart W 2) hr

/-- The actual spectrum map to the x-chart preserves the projective contraction. -/
theorem toX_toCurve {S : Type u} [CommRing S] [Algebra R S]
    (f : Coordinate W s b3 b4 b6 →ₐ[R] S) (a : Sˣ)
    (ha : f (coord W s b3 b4 b6 1) = a) :
    Spec.map (CommRingCat.ofHom (toX W s b3 b4 b6 f a ha).toRingHom) ≫
        WeierstrassModificationX.toCurve W s b3 b4 b6 h3 h4 h6 =
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫ toCurve W s b3 b4 b6 h3 h4 h6 := by
  have hr := congrArg (fun g : WeierstrassIntegralChart.Coordinate W 2 →ₐ[R] S =>
    CommRingCat.ofHom g.toRingHom) (toX_fromOriginal W s b3 b4 b6 h3 h4 h6 f a ha)
  change _ ≫ (Spec.map _ ≫ _) = _ ≫ (Spec.map _ ≫ _)
  simp only [← Category.assoc, ← Spec.map_comp]
  exact congrArg (fun g => Spec.map g ≫ WeierstrassIntegralChart.integralCurveChart W 2) hr

end FLT.Mazur.WeierstrassModificationY
