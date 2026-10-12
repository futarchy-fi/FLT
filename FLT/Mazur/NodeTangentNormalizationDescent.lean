/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentNormalizationOpen

/-!
# Semilinear reflection on the actual normalization open

Extend the constructed normalization involution to D(z(z+a)). It exchanges
the two original tangent factors, inverts their ordered ratio, and agrees
with the original tensor-chart operation on every localized function.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct LaurentPolynomial
namespace FLT.Mazur
open Polynomial WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
local notation "S" => AdjoinRoot (nodeTangentPolynomial W)
local notation "a" => WeierstrassCurve.a₁ (nodeTangentShear W)
local notation "A" => Coordinate W 2
local notation "B" => S ⊗[R] A
local notation "cx" => coord W 2 0
local notation "cy" => coord W 2 1
local notation "U" => nodeTangentTensorOpen W cx cy
/-- Keep the fixed tensor ring structure used by the normalization comparison. -/
local instance normalizationDescentTensorCommRing : CommRing B :=
  normalizationTensorCommRing W
/-- Keep the fixed original tangent localization structure. -/
local instance normalizationDescentOpenCommRing : CommRing U :=
  normalizationTangentOpenCommRing W
local notation "V" => nodeTangentNormalizationOpenRing W
local notation "i" => algebraMap S[X] V
local notation "σ" => nodeTangentNormalizationConjugation W

/-- Extend the actual normalization operation over the invariant complement of the node branches. -/
def nodeTangentNormalizationOpenConjugation : V →+* V :=
  IsLocalization.Away.lift (nodeTangentNormalizationX W)
    (g := (i).comp (σ).toRingHom) (by
      change IsUnit (i (σ (nodeTangentNormalizationX W)))
      rw [nodeTangentNormalizationConjugation_originalX]
      exact IsLocalization.Away.algebraMap_isUnit _)

@[simp] theorem nodeTangentNormalizationOpenConjugation_algebraMap (b : S[X]) :
    nodeTangentNormalizationOpenConjugation W (i b) = i (σ b) :=
  IsLocalization.Away.lift_eq _ _ _

/-- The operation on the normalization open remains an involution. -/
theorem nodeTangentNormalizationOpenConjugation_involutive :
    Function.Involutive (nodeTangentNormalizationOpenConjugation W) := by
  have he : (nodeTangentNormalizationOpenConjugation W).comp
      (nodeTangentNormalizationOpenConjugation W) = RingHom.id V := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (nodeTangentNormalizationX W))
    apply RingHom.ext
    intro b
    simp only [RingHom.comp_apply, nodeTangentNormalizationOpenConjugation_algebraMap,
      RingHom.id_apply, nodeTangentNormalizationConjugation_involutive W b]
  exact RingHom.congr_fun he

/-- The normalized first branch factor goes to the companion factor. -/
theorem nodeTangentNormalizationOpenConjugation_first :
    Units.map (nodeTangentNormalizationOpenConjugation W).toMonoidHom
        (nodeTangentNormalizationFirstUnit W) = nodeTangentNormalizationSecondUnit W := by
  apply Units.ext
  change nodeTangentNormalizationOpenConjugation W
    (nodeTangentNormalizationFirstUnit W : V) = (nodeTangentNormalizationSecondUnit W : V)
  rw [nodeTangentNormalizationFirstUnit_val, nodeTangentNormalizationSecondUnit_val,
    nodeTangentNormalizationOpenConjugation_algebraMap, nodeTangentNormalizationConjugation_X]

/-- The companion factor returns to the first under the same actual operation. -/
theorem nodeTangentNormalizationOpenConjugation_second :
    Units.map (nodeTangentNormalizationOpenConjugation W).toMonoidHom
        (nodeTangentNormalizationSecondUnit W) = nodeTangentNormalizationFirstUnit W := by
  apply Units.ext
  change nodeTangentNormalizationOpenConjugation W
    (nodeTangentNormalizationSecondUnit W : V) = (nodeTangentNormalizationFirstUnit W : V)
  rw [nodeTangentNormalizationSecondUnit_val, nodeTangentNormalizationFirstUnit_val,
    nodeTangentNormalizationOpenConjugation_algebraMap]
  congr 1
  simp only [map_add, nodeTangentNormalizationConjugation_X,
    nodeTangentNormalizationConjugation_C, nodeTangentShear_a₁_conjugate, map_neg]
  ring

/-- The ordered normalization coordinate is inverted, fixing the reflection orientation. -/
theorem nodeTangentNormalizationParameter_conjugate :
    Units.map (nodeTangentNormalizationOpenConjugation W).toMonoidHom
        (nodeTangentNormalizationParameter W) = (nodeTangentNormalizationParameter W)⁻¹ := by
  rw [nodeTangentNormalizationParameter, map_mul, map_inv,
    nodeTangentNormalizationOpenConjugation_first, nodeTangentNormalizationOpenConjugation_second,
    mul_inv_rev, inv_inv]

/-- The coefficient inclusion is the actual root-algebra conjugation. -/
theorem nodeTangentNormalizationOpenConjugation_coeff (c : S) :
    nodeTangentNormalizationOpenConjugation W (algebraMap S V c) =
      algebraMap S V (nodeTangentConjugation W c) := by
  rw [IsScalarTower.algebraMap_apply S S[X] V,
    nodeTangentNormalizationOpenConjugation_algebraMap]
  change i (σ (C c)) = _
  rw [nodeTangentNormalizationConjugation_C]
  rfl

/-- The normalization morphism intertwines the actual original localized tensor operation. -/
theorem nodeTangentNormalizationOpen_conjugate
    (h₃ : W.a₃ = 0) (h₄ : W.a₄ = 0) (h₆ : W.a₆ = 0) :
    (nodeTangentNormalizationOpenConjugation W).comp
        (nodeTangentNormalizationOpen W h₃ h₄ h₆) =
      (nodeTangentNormalizationOpen W h₃ h₄ h₆).comp
        (nodeTangentTensorOpenConjugation W cx cy) := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (nodeTangentTensorFirst W cx cy * nodeTangentTensorSecond W cx cy))
  apply RingHom.ext
  intro b
  simp only [RingHom.comp_apply, nodeTangentNormalizationOpen_algebraMap,
    nodeTangentNormalizationOpenConjugation_algebraMap,
    nodeTangentTensorOpenConjugation_algebraMap]
  exact congrArg i (DFunLike.congr_fun (nodeTangentNormalizationConjugation_tensor W h₃ h₄ h₆) b)

/-- The full Laurent parameter of the original normalization open. -/
def nodeTangentNormalizationLaurent : S[T;T⁻¹] →+* V :=
  LaurentPolynomial.eval₂ (algebraMap S V) (nodeTangentNormalizationParameter W)

/-- The normalization comparison preserves the actual root coefficient inclusion. -/
theorem nodeTangentNormalizationOpen_coeff
    (h₃ : W.a₃ = 0) (h₄ : W.a₄ = 0) (h₆ : W.a₆ = 0) (c : S) :
    nodeTangentNormalizationOpen W h₃ h₄ h₆ (algebraMap S U c) = algebraMap S V c := by
  rw [IsScalarTower.algebraMap_apply S B U, nodeTangentNormalizationOpen_algebraMap]
  change i (nodeTangentNormalizationTensor W h₃ h₄ h₆ (c ⊗ₜ[R] (1 : A))) = _
  rw [nodeTangentNormalizationTensor_tmul, map_one, mul_one]
  rfl

/-- The whole original Laurent parameter map becomes the computed normalization parameter map. -/
theorem nodeTangentNormalizationOpen_laurent
    (h₃ : W.a₃ = 0) (h₄ : W.a₄ = 0) (h₆ : W.a₆ = 0) :
    (nodeTangentNormalizationOpen W h₃ h₄ h₆).comp
        (nodeTangentTensorLaurentParameter W cx cy) = nodeTangentNormalizationLaurent W := by
  have ht := congrArg Units.val (nodeTangentNormalizationOpen_parameter W h₃ h₄ h₆)
  have hi := congrArg (fun t : Vˣ => (t⁻¹ : Vˣ).val)
    (nodeTangentNormalizationOpen_parameter W h₃ h₄ h₆)
  apply PolygonScalingNaturality.ringHom_ext
  · intro c
    simpa only [RingHom.comp_apply, nodeTangentTensorLaurentParameter,
      nodeTangentNormalizationLaurent, LaurentPolynomial.eval₂_C] using
      nodeTangentNormalizationOpen_coeff W h₃ h₄ h₆ c
  · simpa [nodeTangentTensorLaurentParameter, nodeTangentNormalizationLaurent] using ht
  · simpa [nodeTangentTensorLaurentParameter, nodeTangentNormalizationLaurent] using hi

/-- The entire Laurent map, with its actual coefficient map, realizes semilinear reflection. -/
theorem nodeTangentNormalizationLaurent_conjugate :
    (nodeTangentNormalizationOpenConjugation W).comp (nodeTangentNormalizationLaurent W) =
      (nodeTangentNormalizationLaurent W).comp (nodeTangentLaurentTwist W) := by
  have ht := congrArg Units.val (nodeTangentNormalizationParameter_conjugate W)
  have hi := congrArg (fun t : Vˣ => (t⁻¹ : Vˣ).val)
    (nodeTangentNormalizationParameter_conjugate W)
  apply PolygonScalingNaturality.ringHom_ext
  · intro c
    simpa only [RingHom.comp_apply, nodeTangentNormalizationLaurent,
      LaurentPolynomial.eval₂_C, nodeTangentLaurentTwist_C] using
      nodeTangentNormalizationOpenConjugation_coeff W c
  · simpa [nodeTangentNormalizationLaurent] using ht
  · simpa [nodeTangentNormalizationLaurent] using hi

/-- The reflection comparison is an equality of actual affine-scheme morphisms. -/
theorem nodeTangentNormalizationLaurent_spec :
    Spec.map (CommRingCat.ofHom (nodeTangentNormalizationOpenConjugation W)) ≫
        Spec.map (CommRingCat.ofHom (nodeTangentNormalizationLaurent W)) =
      Spec.map (CommRingCat.ofHom (nodeTangentNormalizationLaurent W)) ≫
        Spec.map (CommRingCat.ofHom (nodeTangentLaurentTwist W)) := by
  simpa only [CommRingCat.ofHom_comp, Spec.map_comp] using
    congrArg (fun f => Spec.map (CommRingCat.ofHom f))
      (nodeTangentNormalizationLaurent_conjugate W)

end FLT.Mazur
