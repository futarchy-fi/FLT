/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialTensorSlopeLaurent
public import FLT.Mazur.WeierstrassModificationXBaseChange
public import FLT.Mazur.PrincipalOpenTensorGeometry

/-!
# The initial tensor Laurent comparison is the original geometric boundary

The function map on the full initial chart has exactly the original pair
of integral transition morphisms. All original tensor functions are retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k : ℕ}
  (d : Data W π k) (e : Data W π (k + 1))
  (S : Type u) [CommRing S] [Algebra R S]
  (r : SuccessiveIncidence.Coordinate (algebraMap R S π))
  (hr : r ^ 2 + nodeSlopeLinear (W.map (algebraMap R S))
    (algebraMap R S π) (algebraMap R S e.b3) * r =
    nodeSlopeConstant (W.map (algebraMap R S)) (algebraMap R S (π ^ k))
      (algebraMap R S π) (algebraMap R S e.b4) (algebraMap R S e.b6))
local notation "x" => WeierstrassDilatation.x W (π ^ k) d.b3 d.b4 d.b6
local notation "t₀" => WeierstrassModificationX.t W (π ^ k) d.b3 d.b4 d.b6
local notation "v₀" => WeierstrassModificationX.v W (π ^ k) d.b3 d.b4 d.b6
local notation "A" => PrincipalOpenTensor.transition S x t₀
  (WeierstrassModificationX.overlapEquiv W (π ^ k) d.b3 d.b4 d.b6)
local notation "L" => initialDividedSlopeLaurent hπ d e S r hr

local notation "u₁" => coord W (π ^ k) π e.b3 e.b4 e.b6 2
local notation "a" => WeierstrassModificationX.overlapEquiv W (π ^ k) d.b3 d.b4 d.b6
local notation "b" => previousBoundaryEquiv hπ d e
local notation "T₀" => S ⊗[R] WeierstrassModificationX.Coordinate W (π ^ k)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "E" => initialTensorSlopeLaurent hπ d e S r hr

/-- The function map from the entire original initial tensor chart. -/
def initialTensorSlopeRetraction : T₀ →ₐ[S] S[T;T⁻¹] :=
  (E).comp (IsScalarTower.toAlgHom S T₀ _)

/-- The initial incidence is the original inverse edge parameter on the full tensor chart. -/
theorem initialTensorSlopeRetraction_t :
    initialTensorSlopeRetraction hπ d e S r hr ((1 : S) ⊗ₜ[R] t₀) =
      LaurentPolynomial.T (-1) := by
  change E (algebraMap T₀ _ ((1 : S) ⊗ₜ[R] t₀)) = _
  rw [← PrincipalOpenTensor.coefficient_base, initialTensorSlopeLaurent_t]

/-- The initial slope on the full tensor chart is the original next-branch slope. -/
theorem initialTensorSlopeRetraction_v :
    initialTensorSlopeRetraction hπ d e S r hr ((1 : S) ⊗ₜ[R] v₀) =
      rightIncidenceLaurent (algebraMap R S π) r := by
  change E (algebraMap T₀ _ ((1 : S) ⊗ₜ[R] v₀)) = _
  rw [← PrincipalOpenTensor.coefficient_base, initialTensorSlopeLaurent_v]

/-- The full localized comparison is the original two-transition boundary morphism. -/
@[reassoc] theorem initialTensorSlopeLaurent_spec :
    Spec.map (CommRingCat.ofHom (E).toRingHom) =
      tensorSlopeRightBoundary W (π ^ k) π e.b3 e.b4 e.b6 S r hr ≫
        (PrincipalOpenTensor.transitionIso S x u₁ b).hom ≫
          (PrincipalOpenTensor.transitionIso S x t₀ a).inv := by
  rw [← tensorRightSlopeLaurent_spec]
  rw [initialTensorSlopeLaurent]
  change Spec.map _ = Spec.map _ ≫ Spec.map _ ≫ Spec.map _
  simp only [← Spec.map_comp]
  rfl

/-- Every original initial tensor function has exactly the original boundary restriction. -/
theorem initialTensorSlopeRetraction_spec :
    Spec.map (CommRingCat.ofHom
      (initialTensorSlopeRetraction hπ d e S r hr).toRingHom) =
      tensorSlopeRightBoundary W (π ^ k) π e.b3 e.b4 e.b6 S r hr ≫
        (PrincipalOpenTensor.transitionIso S x u₁ b).hom ≫
          (PrincipalOpenTensor.transitionIso S x t₀ a).inv ≫
            PrincipalOpenTensor.inclusion S t₀ := by
  rw [← initialTensorSlopeLaurent_spec_assoc]
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
