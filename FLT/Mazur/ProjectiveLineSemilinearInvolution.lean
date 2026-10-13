/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineCoefficientEndpoints
public import FLT.Mazur.ProjectiveLineScaledReversalConjugation

/-!
# Involutive semilinear projective reciprocals

Coefficient changes compose contravariantly on both complete charts. A reciprocal
whose constant is fixed by an involutive coefficient map is itself involutive.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.ProjectiveLine
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K L M : Type u} [Field K] [Field L] [Field M]

/-- Identity coefficients act identically on the entire projective line. -/
theorem coefficientMap_id : coefficientMap (RingHom.id K) = 𝟙 _ := by
  apply pushout.hom_ext
  · change left K ≫ _ = left K ≫ _
    rw [left_coefficientMap]
    simp
  · change right K ≫ _ = right K ≫ _
    rw [right_coefficientMap]
    simp

/-- Composition retains the full coefficient map on both charts. -/
@[reassoc] theorem coefficientMap_comp (f : K →+* L) (g : L →+* M) :
    coefficientMap g ≫ coefficientMap f = coefficientMap (g.comp f) := by
  have h : Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom g)) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)) =
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (g.comp f))) := by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext x <;> simp
  apply pushout.hom_ext
  · change left M ≫ _ = left M ≫ _
    rw [left_coefficientMap_assoc, left_coefficientMap, left_coefficientMap,
      ← Category.assoc, h]
  · change right M ≫ _ = right M ≫ _
    rw [right_coefficientMap_assoc, right_coefficientMap, right_coefficientMap,
      ← Category.assoc, h]

/-- Full projective scaling commutes with coefficient change using the mapped unit. -/
@[reassoc] theorem scaling_coefficientMap (f : K →+* L) (a : Kˣ) :
    scaling L (Units.map f a) ≫ coefficientMap f = coefficientMap f ≫ scaling K a := by
  apply pushout.hom_ext
  · change left L ≫ _ = left L ≫ _
    rw [left_scaling_assoc, left_coefficientMap, left_coefficientMap_assoc,
      left_scaling, chartScaling_coefficient_assoc f a _ rfl]
  · change right L ≫ _ = right L ≫ _
    rw [right_scaling_assoc, right_coefficientMap, right_coefficientMap_assoc,
      right_scaling, chartScaling_coefficient_assoc f a⁻¹ _ (map_inv _ _)]

/-- The original reciprocal commutes with coefficients, retaining its mapped constant. -/
@[reassoc] theorem scaledEndpointReversal_coefficientMap (f : K →+* L) (a : Kˣ) :
    scaledEndpointReversal L (Units.map f a) ≫ coefficientMap f =
      coefficientMap f ≫ scaledEndpointReversal K a := by
  rw [scaledEndpointReversal, Category.assoc, scaling_coefficientMap,
    endpointReversal_coefficientMap_assoc, scaledEndpointReversal]

/-- Applying the same full scaled reciprocal twice restores the projective parameter. -/
@[reassoc] theorem scaledEndpointReversal_involutive (a : Kˣ) :
    scaledEndpointReversal K a ≫ scaledEndpointReversal K a = 𝟙 _ := by
  simp only [scaledEndpointReversal, Category.assoc, scaling_endpointReversal_assoc]
  rw [← Category.assoc, endpointReversal_involutive, Category.id_comp,
    ← scaling_mul, inv_mul_cancel, scaling_one]

/-- A coefficient-fixed reciprocal constant gives an actual semilinear involution. -/
@[reassoc] theorem semilinearReciprocal_involutive (f : K →+* K)
    (hf : f.comp f = RingHom.id K) (a : Kˣ) (ha : Units.map f a = a) :
    (coefficientMap f ≫ scaledEndpointReversal K a) ≫
      (coefficientMap f ≫ scaledEndpointReversal K a) = 𝟙 _ := by
  have h := scaledEndpointReversal_coefficientMap f a
  rw [ha] at h
  rw [Category.assoc, ← Category.assoc (scaledEndpointReversal K a), h,
    Category.assoc, scaledEndpointReversal_involutive, Category.comp_id,
    coefficientMap_comp, hf, coefficientMap_id]

end FLT.Mazur.ProjectiveLine
