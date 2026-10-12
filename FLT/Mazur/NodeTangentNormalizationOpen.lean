/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentNormalizationConjugation
public import FLT.Mazur.NodeTangentTensorLaurentDescent

/-!
# The original tangent open in normalization coordinates

The product of the two original tangent factors is x³ on the normalization.
Thus its inverse image is D(x)=D(z(z+a)), and the actual tangent ratio is
the normalized coordinate z/(z+a), with the original coefficient map retained.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur
open Polynomial WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
local notation "S" => AdjoinRoot (nodeTangentPolynomial W)
local notation "a" => WeierstrassCurve.a₁ (nodeTangentShear W)
local notation "x" => nodeTangentNormalizationX W
local notation "A" => Coordinate W 2
local notation "B" => S ⊗[R] A
local notation "cx" => coord W 2 0
local notation "cy" => coord W 2 1
local notation "U" => nodeTangentTensorOpen W cx cy
/-- Freeze the tensor chart ring structure before forming localization maps. -/
local instance normalizationTensorCommRing : CommRing B := inferInstance
/-- Freeze the original tangent localization ring structure. -/
local instance normalizationTangentOpenCommRing : CommRing U := inferInstance

/-- The normalization open above the original smooth affine nodal chart. -/
abbrev nodeTangentNormalizationOpenRing := Localization.Away x
local notation "V" => nodeTangentNormalizationOpenRing W
local notation "i" => algebraMap S[X] V

/-- The normalization coordinate z is a unit off the two node preimages. -/
def nodeTangentNormalizationFirstUnit : Vˣ :=
  (IsLocalization.Away.isUnit_of_dvd («S» := V) x
    (dvd_mul_right (X : S[X]) (X + C a))).unit

/-- The other factor z+a is a unit on the same original inverse-image open. -/
def nodeTangentNormalizationSecondUnit : Vˣ :=
  (IsLocalization.Away.isUnit_of_dvd («S» := V) x
    (dvd_mul_left (X + C a) (X : S[X]))).unit

@[simp] theorem nodeTangentNormalizationFirstUnit_val :
    (nodeTangentNormalizationFirstUnit W : V) = i X := IsUnit.unit_spec _

@[simp] theorem nodeTangentNormalizationSecondUnit_val :
    (nodeTangentNormalizationSecondUnit W : V) = i (X + C a) := IsUnit.unit_spec _

/-- The normalized ordered tangent coordinate z/(z+a). -/
def nodeTangentNormalizationParameter : Vˣ :=
  nodeTangentNormalizationFirstUnit W * (nodeTangentNormalizationSecondUnit W)⁻¹

variable (h₃ : W.a₃ = 0) (h₄ : W.a₄ = 0) (h₆ : W.a₆ = 0)
local notation "f" => nodeTangentNormalizationTensor W h₃ h₄ h₆

/-- The actual original denominator pulls back to x³, so its inverse image is D(x). -/
theorem nodeTangentNormalizationTensor_product :
    f (nodeTangentTensorFirst W cx cy * nodeTangentTensorSecond W cx cy) = x ^ 3 := by
  rw [map_mul, nodeTangentNormalizationTensor_first, nodeTangentNormalizationTensor_second]
  simp only [nodeTangentNormalizationX]
  ring

/-- The normalization map on the original invariant tangent open, constructed by localization. -/
def nodeTangentNormalizationOpen : U →+* V :=
  IsLocalization.Away.lift
    (nodeTangentTensorFirst W cx cy * nodeTangentTensorSecond W cx cy)
    (g := (i).comp (f).toRingHom) (by
      change IsUnit (i (f _))
      rw [nodeTangentNormalizationTensor_product, map_pow]
      exact (IsLocalization.Away.algebraMap_isUnit x).pow 3)

@[simp] theorem nodeTangentNormalizationOpen_algebraMap (b : B) :
    nodeTangentNormalizationOpen W h₃ h₄ h₆ ((algebraMap B U) b) = i (f b) :=
  IsLocalization.Away.lift_eq _ _ _

/-- The first original unit factor has its computed normalization coordinates. -/
theorem nodeTangentNormalizationOpen_first :
    Units.map (nodeTangentNormalizationOpen W h₃ h₄ h₆).toMonoidHom
        (nodeTangentTensorOpenFirstUnit W cx cy) =
      nodeTangentNormalizationFirstUnit W *
        (nodeTangentNormalizationFirstUnit W * nodeTangentNormalizationSecondUnit W) := by
  apply Units.ext
  change nodeTangentNormalizationOpen W h₃ h₄ h₆
    (nodeTangentTensorOpenFirstUnit W cx cy : U) = _
  rw [nodeTangentTensorOpenFirstUnit_val, nodeTangentNormalizationOpen_algebraMap,
    nodeTangentNormalizationTensor_first]
  simp only [Units.val_mul, nodeTangentNormalizationFirstUnit_val,
    nodeTangentNormalizationSecondUnit_val, nodeTangentNormalizationX, map_mul]

/-- The companion original unit factor uses the same original x coordinate. -/
theorem nodeTangentNormalizationOpen_second :
    Units.map (nodeTangentNormalizationOpen W h₃ h₄ h₆).toMonoidHom
        (nodeTangentTensorOpenSecondUnit W cx cy) =
      nodeTangentNormalizationSecondUnit W *
        (nodeTangentNormalizationFirstUnit W * nodeTangentNormalizationSecondUnit W) := by
  apply Units.ext
  change nodeTangentNormalizationOpen W h₃ h₄ h₆
    (nodeTangentTensorOpenSecondUnit W cx cy : U) = _
  rw [nodeTangentTensorOpenSecondUnit_val, nodeTangentNormalizationOpen_algebraMap,
    nodeTangentNormalizationTensor_second]
  simp only [Units.val_mul, nodeTangentNormalizationFirstUnit_val,
    nodeTangentNormalizationSecondUnit_val, nodeTangentNormalizationX, map_mul]

/-- The original first/second tangent ratio becomes exactly z/(z+a). -/
theorem nodeTangentNormalizationOpen_parameter :
    Units.map (nodeTangentNormalizationOpen W h₃ h₄ h₆).toMonoidHom
        (nodeTangentTensorOpenParameter W cx cy) = nodeTangentNormalizationParameter W := by
  rw [nodeTangentTensorOpenParameter, map_mul, map_inv,
    nodeTangentNormalizationOpen_first, nodeTangentNormalizationOpen_second,
    nodeTangentNormalizationParameter]
  group

end FLT.Mazur
