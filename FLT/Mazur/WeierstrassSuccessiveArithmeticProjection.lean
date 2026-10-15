/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveArithmeticRetractionRestriction
public import FLT.Mazur.TensorOpenChart
public import FLT.Mazur.WeierstrassSuccessiveXBaseChange
public import FLT.Mazur.PolygonArithmeticCompleteBaseSquare

/-!
# Original integral projections of the successive arithmetic coordinates

The tensor presentation projects by the actual original coefficient map.
Both this projection and the quotient structure commute with arithmetic
restriction, providing the two components of the global restriction square.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
open PolygonArithmeticStages
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (S : Type u) [CommRing S] [Algebra R S]

/-- The tensor presentation retains the original integral coordinate projection. -/
@[reassoc] theorem baseChangeEquiv_spec_projection :
    Spec.map (CommRingCat.ofHom (baseChangeEquiv W s π b3 b4 b6 S).toRingHom) ≫
      TensorOpenChart.projection =
        Spec.map (CommRingCat.ofHom (coefficientMap W s π b3 b4 b6 S).toRingHom) := by
  rw [TensorOpenChart.projection, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply coefficient_ringHom_ext
  · intro a
    change baseChangeForward W s π b3 b4 b6 S
      ((Algebra.TensorProduct.includeRight : Coordinate W s π b3 b4 b6 →ₐ[R]
        ScalarExtension W s π b3 b4 b6 S) (algebraMap R _ a)) =
          coefficientMap W s π b3 b4 b6 S (algebraMap R _ a)
    rw [AlgHom.commutes, AlgHom.commutes]
    exact ((baseChangeForward W s π b3 b4 b6 S).restrictScalars R).commutes a
  · intro i
    exact (baseChangeForward_coord W s π b3 b4 b6 S i).trans
      (coefficientMap_coord W s π b3 b4 b6 S i).symm

variable (m : ℕ)
local notation "Q₀" => Quotient R π m
local notation "Q₁" => Quotient R π (m + 1)
local notation "q₁" => algebraMap R Q₁
local notation "f" => (AlgHom.toRingHom (restriction R π m))

/-- The original coordinate projection is unchanged by quotient restriction. -/
@[reassoc] theorem arithmeticSuccessiveRestriction_projection :
    arithmeticSuccessiveRestriction R π m W s b3 b4 b6 ≫
      Spec.map (CommRingCat.ofHom (coefficientMap W s π b3 b4 b6 Q₁).toRingHom) =
        Spec.map (CommRingCat.ofHom (coefficientMap W s π b3 b4 b6 Q₀).toRingHom) := by
  rw [arithmeticSuccessiveRestriction, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply coefficient_ringHom_ext
  · intro a
    change coefficientRingMap f (W.map q₁) (q₁ s) (q₁ π) (q₁ b3) (q₁ b4) (q₁ b6)
      (coefficientMap W s π b3 b4 b6 Q₁ (algebraMap R _ a)) =
        coefficientMap W s π b3 b4 b6 Q₀ (algebraMap R _ a)
    rw [AlgHom.commutes, AlgHom.commutes]
    change coefficientRingMap f (W.map q₁) (q₁ s) (q₁ π) (q₁ b3) (q₁ b4) (q₁ b6)
      (algebraMap Q₁ _ (q₁ a)) = algebraMap Q₀ _ (algebraMap R Q₀ a)
    rw [arithmeticCoefficientRingMap_algebraMap]
    exact congrArg (algebraMap Q₀ _) ((restriction R π m).commutes a)
  · intro i
    change coefficientRingMap f (W.map q₁) (q₁ s) (q₁ π) (q₁ b3) (q₁ b4) (q₁ b6)
      (coefficientMap W s π b3 b4 b6 Q₁ (coord W s π b3 b4 b6 i)) =
        coefficientMap W s π b3 b4 b6 Q₀ (coord W s π b3 b4 b6 i)
    simp only [coefficientMap_coord]
    exact arithmeticCoefficientRingMap_coord R π m W s b3 b4 b6 i

/-- The successive arithmetic restriction retains the original quotient coefficient map. -/
@[reassoc] theorem arithmeticSuccessiveRestriction_structure :
    arithmeticSuccessiveRestriction R π m W s b3 b4 b6 ≫
      Spec.map (CommRingCat.ofHom (algebraMap Q₁ (ExtendedCoordinate W s π b3 b4 b6 Q₁))) =
        Spec.map (CommRingCat.ofHom (algebraMap Q₀
          (ExtendedCoordinate W s π b3 b4 b6 Q₀))) ≫ baseRestriction R π m := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (arithmeticCoefficientRingMap_algebraMap R π m W s b3 b4 b6)

end FLT.Mazur.WeierstrassSuccessiveX
