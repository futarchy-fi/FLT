/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXArithmeticRestrictionMaps
public import FLT.Mazur.WeierstrassModificationXBaseChangeGenerators
public import FLT.Mazur.TensorOpenChart
public import FLT.Mazur.PolygonArithmeticCompleteBaseSquare

/-!
# Original projections of the initial arithmetic equation

The tensor presentation retains the original integral coordinate map.
Both integral and coefficient projections commute with quotient restriction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassModificationX
open PolygonArithmeticStages
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (S : Type u) [CommRing S] [Algebra R S]

/-- The full initial tensor comparison retains every original integral function. -/
@[reassoc] theorem baseChangeEquiv_spec_projection :
    Spec.map (CommRingCat.ofHom (baseChangeEquiv W s b3 b4 b6 S).toRingHom) ≫
      TensorOpenChart.projection =
        Spec.map (CommRingCat.ofHom (coefficientMap W s b3 b4 b6 S).toRingHom) := by
  rw [TensorOpenChart.projection, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  change baseChangeEquiv W s b3 b4 b6 S (1 ⊗ₜ[R] z) = coefficientMap W s b3 b4 b6 S z
  rw [baseChangeEquiv_tmul, one_smul]

variable (π : R) (m : ℕ)
local notation "Q₀" => Quotient R π m
local notation "Q₁" => Quotient R π (m + 1)
local notation "q₀" => algebraMap R Q₀
local notation "q₁" => algebraMap R Q₁
local notation "g" => arithmeticInitialCoefficientRingMap R π m W s b3 b4 b6

/-- The full initial quotient map retains its original integral coordinate projection. -/
@[reassoc] theorem arithmeticInitialRestriction_projection :
    arithmeticInitialRestriction R π m W s b3 b4 b6 ≫
      Spec.map (CommRingCat.ofHom (coefficientMap W s b3 b4 b6 Q₁).toRingHom) =
        Spec.map (CommRingCat.ofHom (coefficientMap W s b3 b4 b6 Q₀).toRingHom) := by
  rw [arithmeticInitialRestriction, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply coefficient_ringHom_ext
  · intro a
    change g (coefficientMap W s b3 b4 b6 Q₁ (algebraMap R _ a)) =
      coefficientMap W s b3 b4 b6 Q₀ (algebraMap R _ a)
    rw [AlgHom.commutes, AlgHom.commutes]
    change g (algebraMap Q₁ _ (q₁ a)) = algebraMap Q₀ _ (q₀ a)
    rw [arithmeticInitialCoefficientRingMap_scalar, (restriction R π m).commutes]
  · change g (coefficientMap W s b3 b4 b6 Q₁ (t W s b3 b4 b6)) =
      coefficientMap W s b3 b4 b6 Q₀ (t W s b3 b4 b6)
    rw [coefficientMap_t, coefficientMap_t, arithmeticInitialCoefficientRingMap_t]
  · change g (coefficientMap W s b3 b4 b6 Q₁ (v W s b3 b4 b6)) =
      coefficientMap W s b3 b4 b6 Q₀ (v W s b3 b4 b6)
    rw [coefficientMap_v, coefficientMap_v, arithmeticInitialCoefficientRingMap_v]

/-- The full initial restriction preserves the original arithmetic coefficient projection. -/
@[reassoc] theorem arithmeticInitialRestriction_structure :
    arithmeticInitialRestriction R π m W s b3 b4 b6 ≫
      Spec.map (CommRingCat.ofHom (algebraMap Q₁ (ExtendedCoordinate W s b3 b4 b6 Q₁))) =
        Spec.map (CommRingCat.ofHom (algebraMap Q₀
          (ExtendedCoordinate W s b3 b4 b6 Q₀))) ≫ baseRestriction R π m := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (arithmeticInitialCoefficientRingMap_scalar R π m W s b3 b4 b6)

end FLT.Mazur.WeierstrassModificationX
