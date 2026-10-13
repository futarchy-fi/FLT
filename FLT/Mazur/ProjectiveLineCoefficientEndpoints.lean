/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineCoefficientMap
public import FLT.Mazur.ProjectiveLineEndpointReversal

/-!
# Coefficient change on projective markings and reversal

The full glued coefficient map retains both original marked sections and
commutes with endpoint reversal on the two entire affine charts.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.ProjectiveLine
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K L : Type u} [Field K] [Field L] (f : K →+* L)

/-- Polynomial coefficient change retains the affine origin and its coefficient map. -/
@[reassoc] theorem chartZero_coefficientMap :
    chartZero L ≫ Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)) =
      Spec.map (CommRingCat.ofHom f) ≫ chartZero K := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro x
    simp
  · simp

/-- Coefficient change retains the whole zero section. -/
@[reassoc] theorem zero_coefficientMap :
    zero L ≫ coefficientMap f = Spec.map (CommRingCat.ofHom f) ≫ zero K := by
  rw [zero, Category.assoc, left_coefficientMap, chartZero_coefficientMap_assoc]
  rfl

/-- Coefficient change retains the whole infinity section. -/
@[reassoc] theorem infinity_coefficientMap :
    infinity L ≫ coefficientMap f = Spec.map (CommRingCat.ofHom f) ≫ infinity K := by
  rw [infinity, Category.assoc, right_coefficientMap, chartZero_coefficientMap_assoc]
  rfl

/-- Full coefficient change commutes with the complete projective endpoint reversal. -/
@[reassoc] theorem endpointReversal_coefficientMap :
    endpointReversal L ≫ coefficientMap f = coefficientMap f ≫ endpointReversal K := by
  apply pushout.hom_ext
  · change left L ≫ _ = left L ≫ _
    rw [left_endpointReversal_assoc, right_coefficientMap,
      left_coefficientMap_assoc, left_endpointReversal]
  · change right L ≫ _ = right L ≫ _
    rw [right_endpointReversal_assoc, left_coefficientMap,
      right_coefficientMap_assoc, right_endpointReversal]

end FLT.Mazur.ProjectiveLine
