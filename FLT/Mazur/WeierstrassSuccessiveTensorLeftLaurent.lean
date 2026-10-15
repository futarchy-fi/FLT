/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveTensorLaurentEvaluation
public import FLT.Mazur.WeierstrassSuccessiveXDepthTensorOverlap

/-!
# The original left Laurent parameter on the terminal tensor overlap

The original parameter is retained without edge inversion. The actual depth
transition sends the divided horizontal coordinate to its reciprocal.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct LaurentPolynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (π : R)
  (k : ℕ) (b3 b4 b6 : R) (S : Type u) [CommRing S] [Algebra R S]
  (r : SuccessiveIncidence.Coordinate (algebraMap R S π))
  (hr : r ^ 2 + nodeSlopeLinear (W.map (algebraMap R S))
    (algebraMap R S π) (algebraMap R S b3) * r =
    nodeSlopeConstant (W.map (algebraMap R S)) (algebraMap R S (π ^ k))
      (algebraMap R S π) (algebraMap R S b4) (algebraMap R S b6))
local notation "q" => algebraMap R S
local notation "ev" => tensorSlopePolygonRetraction W (π ^ k) π b3 b4 b6 S r hr
local notation "t" => coord W (π ^ k) π b3 b4 b6 0
local notation "T₀" => ScalarExtension W (π ^ k) π b3 b4 b6 S
local notation "x" => WeierstrassDilatation.x W (π ^ (k + 1)) b3 b4 b6
local notation "y" => WeierstrassDilatation.y W (π ^ (k + 1)) b3 b4 b6
local notation "D" => S ⊗[R] WeierstrassDilatation.Coordinate W (π ^ (k + 1)) b3 b4 b6
local notation "a" => depthOverlapEquiv W π k b3 b4 b6
local notation "A" => PrincipalOpenTensor.transition S x t a

/-- The original left boundary evaluation, without changing its Laurent parameter. -/
def tensorLeftSlopeLaurent : Localization.Away (tensorCoord W (π ^ k) π b3 b4 b6 S 0)
    →ₐ[S] S[T;T⁻¹] :=
  IsLocalization.Away.liftAlgHom (tensorCoord W (π ^ k) π b3 b4 b6 S 0)
    (f := (PolygonSmoothing.leftLaurentMap (q π)).comp ev) (by
      simp only [AlgHom.comp_apply, tensorSlopePolygonRetraction_left,
        PolygonSmoothing.leftLaurentMap_left]
      exact LaurentPolynomial.isUnit_T 1)
local notation "L" => tensorLeftSlopeLaurent W π k b3 b4 b6 S r hr

/-- The original left localization retains every tensor function. -/
theorem tensorLeftSlopeLaurent_base (z : T₀) :
    L (algebraMap _ _ z) = PolygonSmoothing.leftLaurentMap (q π) (ev z) := by
  rw [tensorLeftSlopeLaurent, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

/-- The constructed evaluation is exactly the original left tensor-boundary morphism. -/
theorem tensorLeftSlopeLaurent_spec :
    Spec.map (CommRingCat.ofHom (L).toRingHom) =
      tensorSlopeLeftBoundary W (π ^ k) π b3 b4 b6 S r hr := by
  apply (cancel_mono (PrincipalOpenTensor.inclusion S t)).mp
  rw [tensorSlopeLeftBoundary_inclusion]
  change Spec.map _ ≫ Spec.map _ = (Spec.map _ ≫ Spec.map _) ≫ Spec.map _
  simp only [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  change L (algebraMap T₀ _ z) = PolygonSmoothing.leftPunctureToLaurent (q π)
    (algebraMap _ _ (ev z))
  rw [tensorLeftSlopeLaurent_base, PolygonSmoothing.leftPunctureToLaurent_map]

/-- The original terminal tensor algebra restricted along its actual left depth boundary. -/
def tensorTerminalLaurent : D →ₐ[S] S[T;T⁻¹] :=
  (L).comp ((A).toAlgHom.comp (IsScalarTower.toAlgHom S D _))

/-- The entire algebra restriction is the original integral depth transition on spectra. -/
theorem tensorTerminalLaurent_spec :
    Spec.map (CommRingCat.ofHom
      (tensorTerminalLaurent W π k b3 b4 b6 S r hr).toRingHom) =
      tensorSlopeLeftBoundary W (π ^ k) π b3 b4 b6 S r hr ≫
        (PrincipalOpenTensor.transitionIso S x t a).hom ≫ PrincipalOpenTensor.inclusion S x := by
  rw [← tensorLeftSlopeLaurent_spec]
  change Spec.map _ = Spec.map _ ≫ Spec.map _ ≫ Spec.map _
  simp only [← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassSuccessiveX
