/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationShear
public import FLT.Mazur.WeierstrassModificationXShear
public import FLT.Mazur.WeierstrassModificationXOverlap

/-!
# The original reciprocal overlap commutes with shearing

Check both directions of the actual substitutions (x,y) = (1/t,v/t)
and (t,v) = (1/x,y/x), retaining the full shear parameter.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassModificationX
open WeierstrassDividedDepth
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 r : R)
local notation "U" => rootShearCurve W r
local notation "fX" => shearForward W s b3 b4 b6 r
local notation "fD" => WeierstrassDilatation.shearForward W s b3 b4 b6 r

/-- The forward shear preserves the incidence unit used by the original overlap. -/
theorem shearForward_unit (f : Coordinate U s b3 (b4 - r * b3) b6 →ₐ[R] S)
    (a : Sˣ) (ha : f (t U s b3 (b4 - r * b3) b6) = a) :
    (f.comp fX) (t W s b3 b4 b6) = a := by
  rw [AlgHom.comp_apply, shearForward_t, ha]

/-- The entire map from the divided chart commutes with the original reciprocal gluing. -/
theorem dividedOverlapMap_shear
    (f : Coordinate U s b3 (b4 - r * b3) b6 →ₐ[R] S)
    (a : Sˣ) (ha : f (t U s b3 (b4 - r * b3) b6) = a) :
    (dividedOverlapMap U s b3 (b4 - r * b3) b6 f a ha).comp fD =
      dividedOverlapMap W s b3 b4 b6 (f.comp fX) a
        (shearForward_unit W s b3 b4 b6 r f a ha) := by
  apply WeierstrassDilatation.hom_ext
  · simp only [AlgHom.comp_apply, WeierstrassDilatation.shearForward_x, dividedOverlapMap_x]
  · simp only [AlgHom.comp_apply, WeierstrassDilatation.shearForward_y, map_add, map_mul,
      AlgHom.commutes, dividedOverlapMap_x, dividedOverlapMap_y, shearForward_v]
    ring

/-- The divided-coordinate unit is also preserved before the inverse reciprocal gluing. -/
theorem dividedShearForward_unit
    (f : WeierstrassDilatation.Coordinate U s b3 (b4 - r * b3) b6 →ₐ[R] S)
    (a : Sˣ) (ha : f (WeierstrassDilatation.x U s b3 (b4 - r * b3) b6) = a) :
    (f.comp fD) (WeierstrassDilatation.x W s b3 b4 b6) = a := by
  rw [AlgHom.comp_apply, WeierstrassDilatation.shearForward_x, ha]

/-- The full incidence map commutes with the inverse reciprocal substitution. -/
theorem xOverlapMap_shear
    (f : WeierstrassDilatation.Coordinate U s b3 (b4 - r * b3) b6 →ₐ[R] S)
    (a : Sˣ) (ha : f (WeierstrassDilatation.x U s b3 (b4 - r * b3) b6) = a) :
    (xOverlapMap U s b3 (b4 - r * b3) b6 f a ha).comp fX =
      xOverlapMap W s b3 b4 b6 (f.comp fD) a
        (dividedShearForward_unit W s b3 b4 b6 r f a ha) := by
  apply hom_ext
  · simp only [AlgHom.comp_apply, shearForward_t, xOverlapMap_t]
  · simp only [AlgHom.comp_apply, shearForward_v, map_add, AlgHom.commutes,
      xOverlapMap_v, WeierstrassDilatation.shearForward_y, map_mul, ha]
    rw [mul_add, mul_left_comm (↑a⁻¹ : S), Units.inv_mul, mul_one]

end FLT.Mazur.WeierstrassModificationX
