/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentTensorOrientation
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The genuine conjugation and tangent ratio on the invariant principal open

Localize the original tensor chart where both tangent factors are units.
Their product is fixed by coefficient conjugation, so this open carries an
actual involution. Its constructed unit parameter is sent to its inverse.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur
set_option backward.isDefEq.respectTransparency false
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (W : WeierstrassCurve R) (x y : A)
local notation "L" => AdjoinRoot (nodeTangentPolynomial W)
local notation "B" => L ⊗[R] A
local notation "f₁" => nodeTangentTensorFirst W x y
local notation "f₂" => nodeTangentTensorSecond W x y
local notation "e" => TensorCoefficientSymmetry.equiv (A := A) (nodeTangentConjugation W)

/-- The original chart localized away from the product of its two tangent factors. -/
abbrev nodeTangentTensorOpen := Localization.Away (f₁ * f₂)
local notation "U" => nodeTangentTensorOpen W x y
local notation "i" => algebraMap B U

/-- The actual coefficient conjugation preserves the denominator of the original open. -/
theorem nodeTangentTensorOpen_denominator : IsUnit (i (e (f₁ * f₂))) := by
  rw [nodeTangentTensorProduct_conjugate]
  exact IsLocalization.Away.algebraMap_isUnit (f₁ * f₂)

/-- Extend the original tensor conjugation to the invariant open, without chosen coordinates. -/
def nodeTangentTensorOpenConjugation : U →+* U :=
  IsLocalization.Away.lift (f₁ * f₂)
    (g := (i).comp (e).toRingHom) (nodeTangentTensorOpen_denominator W x y)

/-- The extended operation retains every original localized chart function. -/
@[simp] theorem nodeTangentTensorOpenConjugation_algebraMap (b : B) :
    nodeTangentTensorOpenConjugation W x y (i b) = i (e b) :=
  IsLocalization.Away.lift_eq _ _ _

/-- The extended operation remains an involution on the entire principal-open algebra. -/
theorem nodeTangentTensorOpenConjugation_involutive :
    Function.Involutive (nodeTangentTensorOpenConjugation W x y) := by
  have h : (nodeTangentTensorOpenConjugation W x y).comp
      (nodeTangentTensorOpenConjugation W x y) = RingHom.id U := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (f₁ * f₂))
    apply RingHom.ext
    intro b
    simp only [RingHom.comp_apply, nodeTangentTensorOpenConjugation_algebraMap,
      RingHom.id_apply]
    exact congrArg i (nodeTangentTensorConjugation_involutive W b)
  exact RingHom.congr_fun h

/-- The coefficient operation gives an actual automorphism of the localized chart algebra. -/
def nodeTangentTensorOpenEquiv : U ≃+* U :=
  RingEquiv.ofBijective (nodeTangentTensorOpenConjugation W x y)
    (nodeTangentTensorOpenConjugation_involutive W x y).bijective

/-- The first tangent factor is a constructed unit on this original principal open. -/
def nodeTangentTensorOpenFirstUnit : Uˣ :=
  (IsLocalization.Away.isUnit_of_dvd (S := U) (f₁ * f₂) (dvd_mul_right f₁ f₂)).unit

/-- The second tangent factor is a constructed unit on the same principal open. -/
def nodeTangentTensorOpenSecondUnit : Uˣ :=
  (IsLocalization.Away.isUnit_of_dvd (S := U) (f₁ * f₂) (dvd_mul_left f₂ f₁)).unit

@[simp] theorem nodeTangentTensorOpenFirstUnit_val :
    (nodeTangentTensorOpenFirstUnit W x y : U) = i f₁ := IsUnit.unit_spec _

@[simp] theorem nodeTangentTensorOpenSecondUnit_val :
    (nodeTangentTensorOpenSecondUnit W x y : U) = i f₂ := IsUnit.unit_spec _

/-- The actual tangent ratio on the invariant principal open. -/
def nodeTangentTensorOpenParameter : Uˣ :=
  nodeTangentTensorOpenFirstUnit W x y * (nodeTangentTensorOpenSecondUnit W x y)⁻¹

/-- Coefficient conjugation inverts the constructed parameter on the original open. -/
theorem nodeTangentTensorOpenParameter_conjugate :
    Units.map (nodeTangentTensorOpenConjugation W x y).toMonoidHom
        (nodeTangentTensorOpenParameter W x y) = (nodeTangentTensorOpenParameter W x y)⁻¹ := by
  have hf : Units.map (nodeTangentTensorOpenConjugation W x y).toMonoidHom
      (nodeTangentTensorOpenFirstUnit W x y) = nodeTangentTensorOpenSecondUnit W x y := by
    apply Units.ext
    change nodeTangentTensorOpenConjugation W x y
      (nodeTangentTensorOpenFirstUnit W x y : U) = (nodeTangentTensorOpenSecondUnit W x y : U)
    rw [nodeTangentTensorOpenFirstUnit_val, nodeTangentTensorOpenSecondUnit_val,
      nodeTangentTensorOpenConjugation_algebraMap, nodeTangentTensorFirst_conjugate]
  have hg : Units.map (nodeTangentTensorOpenConjugation W x y).toMonoidHom
      (nodeTangentTensorOpenSecondUnit W x y) = nodeTangentTensorOpenFirstUnit W x y := by
    apply Units.ext
    change nodeTangentTensorOpenConjugation W x y
      (nodeTangentTensorOpenSecondUnit W x y : U) = (nodeTangentTensorOpenFirstUnit W x y : U)
    rw [nodeTangentTensorOpenFirstUnit_val, nodeTangentTensorOpenSecondUnit_val,
      nodeTangentTensorOpenConjugation_algebraMap, nodeTangentTensorSecond_conjugate]
  rw [nodeTangentTensorOpenParameter, map_mul, map_inv, hf, hg, mul_inv_rev, inv_inv]

end FLT.Mazur
