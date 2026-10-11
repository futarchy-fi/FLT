/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveCenterScaling
public import FLT.Mazur.WeierstrassLeftSmoothAffineCenterEquality

/-!
# Translation invariance of the actual successive divided center

An affine presentation of the genuine original smooth translation preserves
(π,x,y) on the preceding divided chart. The proof uses the already constructed
original action and cancels the regular scale from its deeper invariant center.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R]
  (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (h3 : W.a₃ = s * (π * b3)) (h4 : W.a₄ = s * (π * b4))
  (h6 : W.a₆ = s ^ 2 * (π ^ 2 * b6))
local notation "B" =>
  WeierstrassDilatation.Coordinate W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "c" =>
  WeierstrassDilatation.fromOriginal W s (π * b3) (π * b4) (π ^ 2 * b6) h3 h4 h6
variable {S : Type u} [CommRing S] [Algebra R S]
variable (p : Spec (.of S) ⟶ (integralSmoothOpen W).toScheme)
  (α β : WeierstrassDilatation.Coordinate W s
    (π * b3) (π * b4) (π ^ 2 * b6) →ₐ[R] S)
  (hp : p ≫ integralSmoothStructure W =
    (Spec.map (CommRingCat.ofHom (β.comp (WeierstrassDilatation.fromOriginal W s
      (π * b3) (π * b4) (π ^ 2 * b6) h3 h4 h6)).toRingHom) ≫ integralCurveChart W 2) ≫
      integralCurveStructure W)
  (hα : Spec.map (CommRingCat.ofHom (α.comp (WeierstrassDilatation.fromOriginal W s
      (π * b3) (π * b4) (π ^ 2 * b6) h3 h4 h6)).toRingHom) ≫ integralCurveChart W 2 =
    leftSmoothPointAddition W p
      (Spec.map (CommRingCat.ofHom (β.comp (WeierstrassDilatation.fromOriginal W s
      (π * b3) (π * b4) (π ^ 2 * b6) h3 h4 h6)).toRingHom) ≫ integralCurveChart W 2) hp)

include hp hα in
/-- The actual smooth action preserves the entire successive center on divided presentations. -/
theorem successiveSmoothPresentation_center_eq (hs : IsRegular (algebraMap R S s)) :
    (modificationCenter W s π b3 b4 b6).map α.toRingHom =
      (modificationCenter W s π b3 b4 b6).map β.toRingHom := by
  apply successiveCenter_eq_of_originalCenter_eq W s π b3 b4 b6 h3 h4 h6 hs
  apply leftSmoothAffinePresentation_center_eq W (s * π) b3 b4 (s * π * b6)
    (by simpa only [mul_assoc] using h3) (by simpa only [mul_assoc] using h4)
    _ p _ _ hp hα
  calc
    W.a₆ = s ^ 2 * (π ^ 2 * b6) := h6
    _ = s * π * (s * π * b6) := by ring

include hp hα in
/-- Flat coefficient presentations supply regularity without a domain assumption on the source. -/
theorem successiveSmoothPresentation_center_eq_of_flat
    [Module.Flat R S] (hs : IsRegular s) :
    (modificationCenter W s π b3 b4 b6).map α.toRingHom =
      (modificationCenter W s π b3 b4 b6).map β.toRingHom :=
  successiveSmoothPresentation_center_eq W s π b3 b4 b6 h3 h4 h6 p α β hp hα
    (flatRingHom_isRegular (algebraMap R S)
      (RingHom.flat_algebraMap_iff.mpr inferInstance) hs)

include hp hα in
/-- Every graded piece of the successive Rees ideal is preserved on these presentations. -/
theorem successiveSmoothPresentation_center_pow (hs : IsRegular (algebraMap R S s))
    (n : ℕ) :
    (modificationCenter W s π b3 b4 b6 ^ n).map α.toRingHom =
      (modificationCenter W s π b3 b4 b6 ^ n).map β.toRingHom := by
  rw [Ideal.map_pow, Ideal.map_pow,
    successiveSmoothPresentation_center_eq W s π b3 b4 b6 h3 h4 h6 p α β hp hα hs]

end FLT.Mazur.WeierstrassSuccessiveX
