/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearFiniteLineBoundary
public import FLT.Mazur.WeierstrassModificationXTensorOverlapCoordinates
public import FLT.Mazur.PolygonScaledReciprocal
/-!
# Arbitrary-root initial line boundary coordinates

The reverse original incidence transition identifies t with the inverse line
parameter and keeps the full unsheared slope v+r for either tangent branch.
-/

@[expose] public noncomputable section
open Polynomial
open scoped TensorProduct LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k : ℕ}
  (d : Data W π k) (e : Data W π (k + 1))
  (S : Type u) [CommRing S] [Algebra R S] (r : S)
  (hs : algebraMap R S (π ^ k) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S e.b3 = 0) (h4 : algebraMap R S e.b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
open WeierstrassSuccessiveX
open WeierstrassModificationX
set_option quotPrecheck false
local notation "x" => WeierstrassDilatation.x W (π ^ k) d.b3 d.b4 d.b6
local notation "y" => WeierstrassDilatation.y W (π ^ k) d.b3 d.b4 d.b6
local notation "t₀" => t W (π ^ k) d.b3 d.b4 d.b6
local notation "v₀" => WeierstrassModificationX.v W (π ^ k) d.b3 d.b4 d.b6
local notation "A" => S ⊗[R] WeierstrassModificationX.Coordinate W (π ^ k) d.b3 d.b4 d.b6
local notation "Q" => Localization.Away ((1 : S) ⊗ₜ[R] t₀)
local notation "E" => PrincipalOpenTensor.transition S x t₀
  (overlapEquiv W (π ^ k) d.b3 d.b4 d.b6)
variable (v : S) (hv : v * (v + (rootShearCurve (W.map (algebraMap R S)) r).a₁) = 0)
  (scale : Sˣ)
local notation "L" => coefficientShearFiniteLineBoundaryMap hπ d e S r hs hp h3 h4 hr v hv
local notation "ρ" => PolygonScaledReciprocal.reciprocal scale

/-- The original initial boundary through both actual transitions and a signed reciprocal. -/
@[irreducible] def coefficientShearInitialLineBoundaryMap : Q →ₐ[S] S[T;T⁻¹] :=
  ((ρ).comp L).comp (E).symm.toAlgHom

/-- The full incidence coordinate retains the inverse signed reciprocal scale. -/
theorem coefficientShearInitialLineBoundaryMap_t :
    coefficientShearInitialLineBoundaryMap hπ d e S r hs hp h3 h4 hr v hv scale
      (algebraMap A Q ((1 : S) ⊗ₜ[R] t₀)) =
        LaurentPolynomial.C (↑scale⁻¹ : S) * LaurentPolynomial.T 1 := by
  rw [coefficientShearInitialLineBoundaryMap]
  change ρ (L ((E).symm _)) = _
  rw [tensorOverlap_symm_t]
  erw [coefficientShearFiniteLineBoundaryMap_inverse hπ d e S r hs hp h3 h4 hr v hv]
  exact PolygonScaledReciprocal.reciprocal_T_inv scale

/-- The original slope keeps the chosen root shift on every point of the boundary. -/
theorem coefficientShearInitialLineBoundaryMap_v :
    coefficientShearInitialLineBoundaryMap hπ d e S r hs hp h3 h4 hr v hv scale
      (algebraMap A Q ((1 : S) ⊗ₜ[R] v₀)) = LaurentPolynomial.C (v + r) := by
  rw [coefficientShearInitialLineBoundaryMap]
  change ρ (L ((E).symm _)) = _
  rw [tensorOverlap_symm_v, map_mul]
  erw [coefficientShearFiniteLineBoundaryMap_inverse hπ d e S r hs hp h3 h4 hr v hv,
    coefficientShearFiniteLineBoundaryMap_base, tensorShearFiniteLineContraction_y]
  rw [map_mul Polynomial.toLaurent, Polynomial.toLaurent_X, Polynomial.toLaurent_C,
    ← mul_assoc, ← LaurentPolynomial.T_add]
  simp only [neg_add_cancel, LaurentPolynomial.T_zero, one_mul,
    PolygonScaledReciprocal.reciprocal_C]

end FLT.Mazur.WeierstrassDividedDepth
