/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudClosureFactorization

/-!
# Integral coordinate images in a fixed generic algebra

A prescribed generic identification places each model's integral coordinates
in the source generic algebra. Their image is finite and lies in its integral
closure. Integral domination gives inclusion of these actual images.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u
namespace ThreeAdicPlan

variable {R K : Type u} [CommRing R] [Field K] [Algebra R K] [PerfectField K]

/-- Coordinates of the target model, placed in the source's generic algebra. -/
def GenericGaloisHom.integralCoordinateMap {X Y : FF R K} (f : GenericGaloisHom X Y) :
    Y.CoordinateRing →ₐ[R] K ⊗[R] X.CoordinateRing :=
  (f.toBialgHom.toAlgHom.restrictScalars R).comp Algebra.TensorProduct.includeRight

/-- The actual integral coordinate subalgebra for a prescribed generic map. -/
def GenericGaloisHom.integralCoordinateImage {X Y : FF R K} (f : GenericGaloisHom X Y) :
    Subalgebra R (K ⊗[R] X.CoordinateRing) := f.integralCoordinateMap.range

/-- Integral coordinate images are finite modules over the original base. -/
theorem GenericGaloisHom.integralCoordinateImage_finite {X Y : FF R K}
    (f : GenericGaloisHom X Y) : Module.Finite R f.integralCoordinateImage :=
  Module.Finite.of_surjective f.integralCoordinateMap.rangeRestrict.toLinearMap
    f.integralCoordinateMap.rangeRestrict_surjective

/-- Every model's coordinate image lies in the integral closure of the base. -/
theorem GenericGaloisHom.integralCoordinateImage_le_integralClosure {X Y : FF R K}
    (f : GenericGaloisHom X Y) :
    f.integralCoordinateImage ≤ integralClosure R (K ⊗[R] X.CoordinateRing) := by
  rintro a ⟨y, rfl⟩
  exact (Algebra.IsIntegral.isIntegral (R := R) y).map f.integralCoordinateMap

/-- An integral domination map gives inclusion after the prescribed generic identifications. -/
theorem GenericGaloisHom.integralCoordinateImage_le_of_modelHom {X Y Z : FF R K}
    (f : GenericGaloisHom X Y) (g : GenericGaloisHom X Z) (h : ModelHom Z Y)
    (hh : (genericHom h).comp g = f) : f.integralCoordinateImage ≤ g.integralCoordinateImage := by
  rintro a ⟨y, rfl⟩
  refine ⟨h y, ?_⟩
  change g.toBialgHom (1 ⊗ₜ[R] h y) = f.toBialgHom (1 ⊗ₜ[R] y)
  rw [← hh, GenericGaloisHom.toBialgHom_comp, h.toBialgHom_genericHom]
  rfl

variable [IsFractionRing R K]

/-- A generic isomorphism identifies integral coordinates injectively. -/
theorem GenericGaloisHom.integralCoordinateMap_injective {X Y : FF R K}
    (f : GenericGaloisHom X Y) (hf : Function.Surjective f) :
    Function.Injective f.integralCoordinateMap :=
  (f.toBialgHom_injective hf).comp
    (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective R K))

end ThreeAdicPlan
