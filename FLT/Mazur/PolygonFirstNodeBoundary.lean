/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonFirstNodeEndomorphism
public import FLT.Mazur.PolygonFirstNodeLaurent

/-!
# Constructed polynomial boundary coordinates from an original node endomorphism

For an actual endomorphism of xy = e reducing to the identity, the first
Laurent coordinate extends to an explicitly constructed polynomial fixing
its origin. Its vector field is extracted from the genuine node derivation;
no polynomial-extension or origin-vanishing condition is assumed.
-/

@[expose] public noncomputable section
open scoped Polynomial LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing PolygonNodeEqualizer PolygonNodeLocalization
open PolygonScalingNaturality
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
variable (R : Type) [CommRing R]
local notation "S" => Ring R 1
local notation "e" => parameter R 1
local notation "B" => ChartRing (e)
variable (f : ChartRing (parameter R 1) →ₐ[Ring R 1] ChartRing (parameter R 1))
  (hf : ∀ z, firstNodeReduction R (f z) = firstNodeReduction R z)

/-- The polynomial vector field extracted on the first branch of the original node. -/
def firstNodeBoundaryField : R[X] :=
  first (specialFiberEquiv R (firstNodeReduction R
    (firstNodeDifference R f hf (leftCoordinate (e)))))

/-- The extracted field is the first coordinate of the constructed original node derivation. -/
theorem firstNodeBoundaryField_derivation :
    firstNodeBoundaryField R f hf = first (firstNodeEqualizerDerivation R f hf x) := by
  change first _ = first (specialFiberEquiv R
    (firstNodeDifferenceDerivation R f hf ((specialFiberEquiv R).symm x)))
  rw [← specialFiberEquiv_left R, AlgEquiv.symm_apply_apply]
  rw [firstNodeDifferenceDerivation, derivationOfCoordinates_left]

/-- The original node equation forces the constructed boundary origin to be fixed. -/
theorem firstNodeBoundaryField_coeff_zero : (firstNodeBoundaryField R f hf).coeff 0 = 0 := by
  rw [firstNodeBoundaryField_derivation]
  exact NodeDerivationBoundary.first_derivation_x_coeff_zero _

/-- An explicit boundary coordinate over the full first-order coefficient ring. -/
def firstNodeBoundaryPolynomial : (S)[X] :=
  Polynomial.X + Polynomial.C (e) *
    (firstNodeBoundaryField R f hf).map (algebraMap R (S))

/-- The constructed first-order boundary coordinate fixes its boundary origin exactly. -/
theorem firstNodeBoundaryPolynomial_coeff_zero :
    (firstNodeBoundaryPolynomial R f hf).coeff 0 = 0 := by
  simp only [firstNodeBoundaryPolynomial, Polynomial.coeff_add, Polynomial.coeff_X_zero,
    Polynomial.coeff_C_mul, Polynomial.coeff_map, firstNodeBoundaryField_coeff_zero,
    map_zero, mul_zero, add_zero]

/-- Restriction recovers the original node endomorphism, with all first-order coefficients. -/
theorem firstNodeBoundaryPolynomial_toLaurent :
    Polynomial.toLaurent (firstNodeBoundaryPolynomial R f hf) =
      leftLaurentMap (e) (f (leftCoordinate (e))) := by
  let a := firstNodeDifference R f hf (leftCoordinate (e))
  have hx : f (leftCoordinate (e)) = leftCoordinate (e) + algebraMap (S) (B) (e) * a := by
    have he := (Algebra.smul_def (e) a).symm.trans
      (firstNodeDifference_spec R f hf (leftCoordinate (e)))
    exact (sub_eq_iff_eq_add.mp he.symm).trans (add_comm _ _)
  rw [hx, map_add, map_mul, leftLaurentMap_left, AlgHom.commutes]
  change Polynomial.toLaurent (firstNodeBoundaryPolynomial R f hf) =
    LaurentPolynomial.T 1 + LaurentPolynomial.C (e) * leftLaurentMap (e) a
  rw [firstNode_parameter_leftLaurent]
  simp only [firstNodeBoundaryPolynomial, map_add, map_mul,
    Polynomial.toLaurent_X, Polynomial.toLaurent_C]
  congr 2
  exact (RingHom.congr_fun (coeffMap_toLaurent (algebraMap R (S)))
    (firstNodeBoundaryField R f hf)).symm

end FLT.Mazur.PolygonInfinitesimalStages
