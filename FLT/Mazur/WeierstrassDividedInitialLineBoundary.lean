/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXTensorOverlapCoordinates
public import FLT.Mazur.WeierstrassModificationXBaseChange
public import FLT.Mazur.WeierstrassDividedFiniteLineBoundaryGeometry

/-!
# The first retained lines on the original initial tensor boundary

The actual line boundary passes through the reverse initial transition.
Its incidence and slope retain the arbitrary reciprocal scale and tangent root.
-/

@[expose] public noncomputable section
open IsLocalRing Polynomial
open scoped TensorProduct LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (h1 : 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + 1) ≤ depth)
open WeierstrassModificationX
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "x" => WeierstrassDilatation.x W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "t₀" => t W (π ^ start) (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "v₀" => v W (π ^ start) (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "A" => K ⊗[R] Coordinate W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "Q" => Localization.Away ((1 : K) ⊗ₜ[R] t₀)
local notation "e" => PrincipalOpenTensor.transition K x t₀
  (overlapEquiv W (π ^ start) (Data.b3 d) (Data.b4 d) (Data.b6 d))
variable (r : ResidueField R) (hr : r * (r + residue R W.a₁) = 0)
  (scale : (ResidueField R)ˣ)
local notation "L" => residueFiniteLineBoundaryMap hπ data D 0 h1 hstart hk r hr
local notation "ρ" => PolygonScaledReciprocal.reciprocal scale

/-- The actual first line boundary, transported through the original initial transition. -/
def initialLineBoundaryMap : Q →ₐ[K] K[T;T⁻¹] :=
  ((ρ).comp L).comp (e).symm.toAlgHom

/-- The original initial incidence keeps the inverse reciprocal scale. -/
theorem initialLineBoundaryMap_t :
    initialLineBoundaryMap hπ data D h1 hstart hk r hr scale
      (algebraMap A Q ((1 : K) ⊗ₜ[R] t₀)) =
        LaurentPolynomial.C (↑scale⁻¹ : K) * LaurentPolynomial.T 1 := by
  change ρ (L ((e).symm _)) = _
  rw [tensorOverlap_symm_t]
  erw [residueFiniteLineBoundaryMap_inverse hπ data D 0 h1 hstart hk r hr]
  exact PolygonScaledReciprocal.reciprocal_T_inv scale

/-- The original initial slope is the same chosen root on the entire Laurent boundary. -/
theorem initialLineBoundaryMap_v :
    initialLineBoundaryMap hπ data D h1 hstart hk r hr scale
      (algebraMap A Q ((1 : K) ⊗ₜ[R] v₀)) = LaurentPolynomial.C r := by
  change ρ (L ((e).symm _)) = _
  rw [tensorOverlap_symm_v, map_mul]
  erw [residueFiniteLineBoundaryMap_inverse hπ data D 0 h1 hstart hk r hr,
    residueFiniteLineBoundaryMap_base, residueFiniteLineContraction_y]
  rw [map_mul Polynomial.toLaurent, Polynomial.toLaurent_X, Polynomial.toLaurent_C,
    ← mul_assoc, ← LaurentPolynomial.T_add]
  simp only [neg_add_cancel, LaurentPolynomial.T_zero, one_mul,
    PolygonScaledReciprocal.reciprocal_C]

end FLT.Mazur.WeierstrassDividedDepth
