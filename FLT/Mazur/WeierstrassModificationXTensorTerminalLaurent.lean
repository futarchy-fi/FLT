/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXTensorLaurentEvaluation
public import FLT.Mazur.WeierstrassModificationXTensorOverlapCoordinates
public import FLT.Mazur.PrincipalOpenTensorGeometry

/-!
# The original initial Laurent boundary transported to the terminal tensor chart

The full original overlap equivalence transports every function. The initial
incidence parameter becomes the reciprocal terminal abscissa.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial TensorProduct
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (S : Type u) [CommRing S] [Algebra R S]
  (r : S[T;T⁻¹])
  (hr : r ^ 2 + laurentSlopeLinear (W.map (algebraMap R S)) (algebraMap R S b3) * r =
    laurentSlopeConstant (W.map (algebraMap R S)) (algebraMap R S s)
      (algebraMap R S b4) (algebraMap R S b6))
local notation "A" => S ⊗[R] Coordinate W s b3 b4 b6
local notation "D" => S ⊗[R] WeierstrassDilatation.Coordinate W s b3 b4 b6
local notation "t₀" => t W s b3 b4 b6
local notation "x" => WeierstrassDilatation.x W s b3 b4 b6
local notation "a" => overlapEquiv W s b3 b4 b6
local notation "E" => tensorLaurentSlopeEvaluation W s b3 b4 b6 S r hr

/-- Localize the full original tensor Laurent evaluation at the incidence coordinate. -/
def tensorInitialLaurentLocalization :
    Localization.Away ((1 : S) ⊗ₜ[R] t₀) →ₐ[S] S[T;T⁻¹] :=
  IsLocalization.Away.liftAlgHom ((1 : S) ⊗ₜ[R] t₀) (f := E)
    (by rw [tensorLaurentSlopeEvaluation_t]; exact LaurentPolynomial.isUnit_T (-1))
local notation "L" => tensorInitialLaurentLocalization W s b3 b4 b6 S r hr

/-- The localized boundary retains every function of the original initial tensor chart. -/
theorem tensorInitialLaurentLocalization_base (z : A) : L (algebraMap A _ z) = E z := by
  rw [tensorInitialLaurentLocalization, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

/-- The full initial Laurent boundary evaluated on the original terminal tensor chart. -/
def tensorInitialTerminalLaurent : D →ₐ[S] S[T;T⁻¹] :=
  (L).comp ((PrincipalOpenTensor.transition S x t₀ a).toAlgHom.comp
    (Algebra.algHom S D (Localization.Away ((1 : S) ⊗ₜ[R] x))))

attribute [local irreducible] tensorInitialLaurentLocalization tensorLaurentSlopeEvaluation
  tensorInitialTerminalLaurent

/-- The localized map is exactly the original initial boundary on schemes. -/
@[reassoc] theorem tensorInitialLaurentLocalization_spec :
    Spec.map (CommRingCat.ofHom (L).toRingHom) ≫ PrincipalOpenTensor.inclusion S t₀ =
      Spec.map (CommRingCat.ofHom (E).toRingHom) := by
  rw [PrincipalOpenTensor.inclusion, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact RingHom.ext (tensorInitialLaurentLocalization_base W s b3 b4 b6 S r hr)

/-- The full terminal evaluation follows the unchanged original modification transition. -/
@[reassoc] theorem tensorInitialTerminalLaurent_spec :
    Spec.map (CommRingCat.ofHom
      (tensorInitialTerminalLaurent W s b3 b4 b6 S r hr).toRingHom) =
      Spec.map (CommRingCat.ofHom (L).toRingHom) ≫
        (PrincipalOpenTensor.transitionIso S x t₀ a).hom ≫
          PrincipalOpenTensor.inclusion S x := by
  rw [tensorInitialTerminalLaurent]
  change Spec.map _ = Spec.map _ ≫ Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassModificationX
