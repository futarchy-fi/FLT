/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonTopNodeEndomorphism
public import FLT.Mazur.PolygonTopNodeLaurent

/-!
# Constructed polynomial boundary coordinates from an original node endomorphism

For an actual endomorphism of xy = e trivial at the preceding stage, the
top-weight Laurent coordinate extends to an explicitly constructed polynomial fixing
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
variable (R : Type) [CommRing R] (m : ℕ)
local notation "S" => Ring R (m + 1)
local notation "e" => parameter R (m + 1)
local notation "B" => ChartRing (e)
variable (f : ChartRing (parameter R (m + 1)) →ₐ[Ring R (m + 1)] ChartRing (parameter R (m + 1)))
  (hf : ∀ z, topNodeRestriction R m (f z) = topNodeRestriction R m z)

/-- The polynomial vector field extracted on the first branch of the original node. -/
def topNodeBoundaryField : R[X] :=
  first (specialFiberEquiv R (topNodeReduction R m
    (topNodeDifference R m f hf (leftCoordinate (e)))))

/-- The extracted field is the first coordinate of the constructed original node derivation. -/
theorem topNodeBoundaryField_derivation :
    topNodeBoundaryField R m f hf = first (topNodeEqualizerDerivation R m f hf x) := by
  change first _ = first (specialFiberEquiv R
    (topNodeDifferenceDerivation R m f hf ((specialFiberEquiv R).symm x)))
  rw [← specialFiberEquiv_left R, AlgEquiv.symm_apply_apply]
  rw [topNodeDifferenceDerivation, derivationOfCoordinates_left]

/-- The original node equation forces the constructed boundary origin to be fixed. -/
theorem topNodeBoundaryField_coeff_zero : (topNodeBoundaryField R m f hf).coeff 0 = 0 := by
  rw [topNodeBoundaryField_derivation]
  exact NodeDerivationBoundary.first_derivation_x_coeff_zero _

/-- An explicit boundary coordinate over the full top-weight coefficient ring. -/
def topNodeBoundaryPolynomial : (S)[X] :=
  Polynomial.X + Polynomial.C ((e) ^ (m + 1)) *
    (topNodeBoundaryField R m f hf).map (algebraMap R (S))

/-- The constructed top-weight boundary coordinate fixes its boundary origin exactly. -/
theorem topNodeBoundaryPolynomial_coeff_zero :
    (topNodeBoundaryPolynomial R m f hf).coeff 0 = 0 := by
  simp only [topNodeBoundaryPolynomial, Polynomial.coeff_add, Polynomial.coeff_X_zero,
    Polynomial.coeff_C_mul, Polynomial.coeff_map, topNodeBoundaryField_coeff_zero,
    map_zero, mul_zero, add_zero]

/-- Restriction recovers the original node endomorphism, with all top-weight coefficients. -/
theorem topNodeBoundaryPolynomial_toLaurent :
    Polynomial.toLaurent (topNodeBoundaryPolynomial R m f hf) =
      leftLaurentMap (e) (f (leftCoordinate (e))) := by
  let a := topNodeDifference R m f hf (leftCoordinate (e))
  have hx : f (leftCoordinate (e)) =
      leftCoordinate (e) + algebraMap (S) (B) ((e) ^ (m + 1)) * a := by
    have he := (Algebra.smul_def ((e) ^ (m + 1)) a).symm.trans
      (topNodeDifference_spec R m f hf (leftCoordinate (e)))
    exact (sub_eq_iff_eq_add.mp he.symm).trans (add_comm _ _)
  rw [hx, map_add, map_mul, leftLaurentMap_left, AlgHom.commutes]
  change Polynomial.toLaurent (topNodeBoundaryPolynomial R m f hf) =
    LaurentPolynomial.T 1 + LaurentPolynomial.C ((e) ^ (m + 1)) * leftLaurentMap (e) a
  rw [topNode_parameter_leftLaurent]
  simp only [topNodeBoundaryPolynomial, map_add, map_mul,
    Polynomial.toLaurent_X, Polynomial.toLaurent_C]
  congr 2
  exact (RingHom.congr_fun (coeffMap_toLaurent (algebraMap R (S)))
    (topNodeBoundaryField R m f hf)).symm

end FLT.Mazur.PolygonInfinitesimalStages
