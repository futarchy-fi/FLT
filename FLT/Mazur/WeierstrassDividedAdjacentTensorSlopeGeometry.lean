/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAdjacentTensorSlope
public import FLT.Mazur.PrincipalOpenTensorGeometry

/-!
# Original adjacent tensor transitions as polygon branch morphisms

The full tensor Laurent square identifies the actual transition with edge
inversion. Composing with the original inclusion factors through the older
constructed slope branch, without replacing either integral overlap.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) (k : ℕ)
  (d : Data W π (k + 1)) (e : Data W π (k + 1 + 1))
  (S : Type u) [CommRing S] [Algebra R S]
  (r₀ r₁ : SuccessiveIncidence.Coordinate (algebraMap R S π))
  (h₀ : r₀ ^ 2 + nodeSlopeLinear (W.map (algebraMap R S))
    (algebraMap R S π) (algebraMap R S d.b3) * r₀ =
    nodeSlopeConstant (W.map (algebraMap R S)) (algebraMap R S (π ^ k))
      (algebraMap R S π) (algebraMap R S d.b4) (algebraMap R S d.b6))
  (h₁ : r₁ ^ 2 + nodeSlopeLinear (W.map (algebraMap R S))
    (algebraMap R S π) (algebraMap R S e.b3) * r₁ =
    nodeSlopeConstant (W.map (algebraMap R S)) (algebraMap R S (π ^ (k + 1)))
      (algebraMap R S π) (algebraMap R S e.b4) (algebraMap R S e.b6))
  (h : inverseLeftIncidenceLaurent (algebraMap R S π) r₀ =
    rightIncidenceLaurent (algebraMap R S π) r₁)
local notation "x" => WeierstrassDilatation.x W (π ^ (k + 1)) d.b3 d.b4 d.b6
local notation "t" => coord W (π ^ k) π d.b3 d.b4 d.b6 0
local notation "u" => coord W (π ^ (k + 1)) π e.b3 e.b4 e.b6 2
local notation "A" => PrincipalOpenTensor.transitionIso S x t
  (depthOverlapEquiv W π k d.b3 d.b4 d.b6)
local notation "B" => PrincipalOpenTensor.transitionIso S x u (previousBoundaryEquiv hπ d e)
local notation "L" => tensorInverseLeftSlopeLaurent W (π ^ k) π d.b3 d.b4 d.b6 S r₀ h₀
local notation "U" => tensorRightSlopeLaurent W (π ^ (k + 1)) π e.b3 e.b4 e.b6 S r₁ h₁

include h in
/-- The genuine tensor boundary transition is the original polygon edge inversion. -/
@[reassoc] theorem adjacentTensorSlope_boundary :
    tensorSlopeRightBoundary W (π ^ (k + 1)) π e.b3 e.b4 e.b6 S r₁ h₁ ≫
      (B).hom ≫ (A).inv =
    (PolygonSmoothing.edgeInversion S).hom ≫
      tensorSlopeLeftBoundary W (π ^ k) π d.b3 d.b4 d.b6 S r₀ h₀ := by
  rw [← tensorRightSlopeLaurent_spec, ← tensorInverseLeftSlopeLaurent_spec]
  have he : Spec.map (CommRingCat.ofHom (U).toRingHom) ≫ (B).hom =
      Spec.map (CommRingCat.ofHom (L).toRingHom) ≫ (A).hom := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    simp only [← Spec.map_comp]
    exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f.toRingHom))
      (adjacentTensorSlope_transition hπ k d e S r₀ r₁ h₀ h₁ h).symm
  rw [← Category.assoc, he, Category.assoc, Iso.hom_inv_id, Category.comp_id]

include h in
/-- The full original tensor boundary factors through the specified older polygon branch. -/
@[reassoc] theorem adjacentTensorSlope_factorization :
    tensorSlopeRightBoundary W (π ^ (k + 1)) π e.b3 e.b4 e.b6 S r₁ h₁ ≫
      (B).hom ≫ (A).inv ≫ PrincipalOpenTensor.inclusion S t =
    (PolygonSmoothing.edgeInversion S).hom ≫
      PolygonSmoothing.leftBranchOpen S (algebraMap R S π) ≫
        Spec.map (CommRingCat.ofHom
          (tensorSlopePolygonRetraction W (π ^ k) π d.b3 d.b4 d.b6 S r₀ h₀).toRingHom) := by
  rw [adjacentTensorSlope_boundary_assoc hπ k d e S r₀ r₁ h₀ h₁ h,
    tensorSlopeLeftBoundary_inclusion]

end FLT.Mazur.WeierstrassDividedDepth
