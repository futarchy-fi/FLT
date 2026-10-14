/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticCoefficientSmoothSections
public import FLT.Mazur.EllipticE0GeometricGroup
public import FLT.Mazur.EllipticIntegralSectionIdentity

/-!
# The actual coefficient restriction of E₀ preserves its original group law

The coefficient section construction respects the independently constructed
smooth zero and addition. This gives an arithmetic homomorphism to the
intrinsic coefficient smooth group, with its original scheme-valued points.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped MonObj
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (S : Type u) [CommRing S] [Algebra A S]
local notation "V" => W.map (algebraMap A S)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap A S))
local notation "H" => originalSmoothCoefficientMap_isPullback S W
local notation "e" => e0SmoothCoefficientSection A W S

/-- The coefficient section of the original identity is the actual smooth identity section. -/
theorem e0SmoothCoefficientSection_zero : e 0 = integralSmoothZero V := by
  apply (H).hom_ext
  · rw [e0SmoothCoefficientSection_projection, e0SmoothSectionEquiv_zero,
      originalSmoothCoefficientMap_zero]
  · rw [e0SmoothCoefficientSection_structure, integralSmoothZero_structure]

/-- Arithmetic addition specializes to the independently constructed geometric coefficient sum. -/
theorem e0SmoothCoefficientSection_add (P Q : ellipticE0 A W) :
    e (P + Q) = smoothPairPointAddition V (e P) (e Q)
      ((e0SmoothCoefficientSection_structure A W S P).trans
        (e0SmoothCoefficientSection_structure A W S Q).symm) := by
  have hsum : (e0SmoothSectionEquiv A W (P + Q)).left =
      smoothPairPointAddition W (e0SmoothSectionEquiv A W P).left
        (e0SmoothSectionEquiv A W Q).left
        ((e0SmoothSectionEquiv A W P).w.trans (e0SmoothSectionEquiv A W Q).w.symm) :=
    congrArg Over.Hom.left (e0ToSmoothSection_add A W P Q)
  apply (H).hom_ext
  · simp only [e0SmoothCoefficientSection_projection,
      originalSmoothCoefficientMap_pointAddition, hsum]
    exact (WeierstrassGlobalModification.smoothPairPointAddition_comp W q
      (e0SmoothSectionEquiv A W P).left (e0SmoothSectionEquiv A W Q).left
      ((e0SmoothSectionEquiv A W P).w.trans (e0SmoothSectionEquiv A W Q).w.symm)).symm
  · rw [e0SmoothCoefficientSection_structure, smoothPairPointAddition_structure,
      e0SmoothCoefficientSection_structure]

/-- Original E₀ specializes homomorphically into the actual coefficient smooth section group. -/
def e0SmoothCoefficientSectionHom : ellipticE0 A W →+
    Additive (Over.mk (𝟙 (Spec (.of S))) ⟶ (integralSmoothGroup V).X) where
  toFun P := Additive.ofMul
    (Over.homMk (e P) (e0SmoothCoefficientSection_structure A W S P))
  map_zero' := by
    apply Over.OverMorphism.ext
    change e 0 = 𝟙 _ ≫ integralSmoothZero V
    rw [Category.id_comp, e0SmoothCoefficientSection_zero]
  map_add' P Q := by
    apply Over.OverMorphism.ext
    exact e0SmoothCoefficientSection_add A W S P Q

/-- The homomorphism retains the exact geometric coefficient restriction of the integral section. -/
theorem e0SmoothCoefficientSectionHom_left (P : ellipticE0 A W) :
    (e0SmoothCoefficientSectionHom A W S P).toMul.left = e P := rfl

end FLT.Mazur.WeierstrassDividedDepth
