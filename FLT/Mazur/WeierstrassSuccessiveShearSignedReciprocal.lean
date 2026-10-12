/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearBoundaryCoordinates
public import FLT.Mazur.WeierstrassSuccessiveXConicPuncturedParameters
public import FLT.Mazur.PolygonScaledReciprocal

/-!
# Signed reciprocal comparison on every original divided tensor function

The conic punctures have horizontal coordinates a⁻¹/z and -a⁻¹/z. Their
unsheared slopes are r and r-a. A line contraction with those original x,y
coordinates therefore agrees on the whole tensor algebra, not only on points.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassDividedDepth WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
section Boundary
variable {S : Type*} [CommRing S] (U : WeierstrassCurve S) (c : S)
  (a : Sˣ) (ha : (a : S) = U.a₁) (hc : c = 0)
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "u" => conicBoundaryUnit U c

/-- The first original conic puncture has the positive inverse tangent scale. -/
theorem conicBoundaryFirst_inverse_eq :
    conicBoundaryFirst U c hu hc (↑u⁻¹) =
      LaurentPolynomial.C (↑a⁻¹ : S) * LaurentPolynomial.T (-1) := by
  apply (a.isUnit.map (LaurentPolynomial.C (R := S))).mul_right_cancel
  have H : conicBoundaryFirst U c hu hc (↑u⁻¹) * LaurentPolynomial.C (a : S) =
      LaurentPolynomial.T (-1) := by
    calc _ = conicBoundaryFirst U c hu hc (↑u⁻¹) * LaurentPolynomial.C U.a₁ :=
        congrArg (fun z => conicBoundaryFirst U c hu hc (↑u⁻¹) * LaurentPolynomial.C z) ha
      _ = _ := conicBoundaryFirst_inverse_mul U c hu hc
  rw [H]
  calc LaurentPolynomial.T (-1) =
      (LaurentPolynomial.C (↑a⁻¹ : S) * LaurentPolynomial.C (a : S)) *
        LaurentPolynomial.T (-1) := by rw [← map_mul, Units.inv_mul, map_one, one_mul]
    _ = _ := by ring

/-- The opposite original puncture has the negative inverse tangent scale. -/
theorem conicBoundarySecond_inverse_eq :
    conicBoundarySecond U c hu hc (↑u⁻¹) =
      LaurentPolynomial.C (↑(-a)⁻¹ : S) * LaurentPolynomial.T (-1) := by
  apply ((-a).isUnit.map (LaurentPolynomial.C (R := S))).mul_right_cancel
  have hneg : LaurentPolynomial.C (↑(-a) : S) = -LaurentPolynomial.C U.a₁ := by
    rw [Units.val_neg, map_neg, ha]
  rw [hneg, conicBoundarySecond_inverse_mul]
  rw [← hneg]
  calc LaurentPolynomial.T (-1) =
      (LaurentPolynomial.C (↑(-a)⁻¹ : S) * LaurentPolynomial.C (↑(-a) : S)) *
        LaurentPolynomial.T (-1) := by rw [← map_mul, Units.inv_mul, map_one, one_mul]
    _ = _ := by ring

end Boundary

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (S : Type u) [CommRing S] [Algebra R S] (r : S)
  (hs : algebraMap R S s = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S b3 = 0) (h4 : algebraMap R S b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "U₀" => rootShearCurve (W.map (algebraMap R S)) r
local notation "c₀" => algebraMap R S b6
local notation "T₀" => WeierstrassDilatation.ScalarExtension W (s * π) b3 b4 b6 S
local notation "tx" => WeierstrassDilatation.tensorX W (s * π) b3 b4 b6 S
local notation "ty" => WeierstrassDilatation.tensorY W (s * π) b3 b4 b6 S
local notation "φ" => tensorShearDividedConicMap W s π b3 b4 b6 S r hs hp h3 h4 hr
variable (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
  (hc : algebraMap R S b6 = 0)
local notation "hu₀" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)

/-- Positive reciprocal agreement holds on every original divided tensor function. -/
theorem tensorShearConicFirst_reciprocal
    (l : T₀ →ₐ[S] Polynomial S) (hx : l tx = Polynomial.X)
    (hy : l ty = Polynomial.X * Polynomial.C r) :
    (conicBoundaryFirst U₀ c₀ hu₀ hc).comp φ =
      (PolygonScaledReciprocal.reciprocal a⁻¹).comp (Polynomial.toLaurentAlg.comp l) := by
  apply Algebra.TensorProduct.ext_ring
  apply WeierstrassDilatation.hom_ext
  · change conicBoundaryFirst U₀ c₀ hu₀ hc (φ tx) =
      PolygonScaledReciprocal.reciprocal a⁻¹ (Polynomial.toLaurent (l tx))
    rw [tensorShearDividedConicMap_x, conicBoundaryFirst_inverse_eq U₀ c₀ a ha hc,
      hx, Polynomial.toLaurent_X, PolygonScaledReciprocal.reciprocal_T]
  · change conicBoundaryFirst U₀ c₀ hu₀ hc (φ ty) =
      PolygonScaledReciprocal.reciprocal a⁻¹ (Polynomial.toLaurent (l ty))
    rw [tensorShearDividedConicMap_y, map_mul, map_add, conicBoundaryFirst_v,
      AlgHom.commutes, zero_add, conicBoundaryFirst_inverse_eq U₀ c₀ a ha hc,
      hy, map_mul, Polynomial.toLaurent_X, Polynomial.toLaurent_C,
      map_mul, PolygonScaledReciprocal.reciprocal_T, PolygonScaledReciprocal.reciprocal_C]
    rfl

/-- Negative reciprocal agreement keeps the opposite original slope on the whole algebra. -/
theorem tensorShearConicSecond_reciprocal
    (l : T₀ →ₐ[S] Polynomial S) (hx : l tx = Polynomial.X)
    (hy : l ty = Polynomial.X * Polynomial.C (-(U₀).a₁ + r)) :
    (conicBoundarySecond U₀ c₀ hu₀ hc).comp φ =
      (PolygonScaledReciprocal.reciprocal (-a)⁻¹).comp (Polynomial.toLaurentAlg.comp l) := by
  apply Algebra.TensorProduct.ext_ring
  apply WeierstrassDilatation.hom_ext
  · change conicBoundarySecond U₀ c₀ hu₀ hc (φ tx) =
      PolygonScaledReciprocal.reciprocal (-a)⁻¹ (Polynomial.toLaurent (l tx))
    rw [tensorShearDividedConicMap_x, conicBoundarySecond_inverse_eq U₀ c₀ a ha hc,
      hx, Polynomial.toLaurent_X, PolygonScaledReciprocal.reciprocal_T]
  · change conicBoundarySecond U₀ c₀ hu₀ hc (φ ty) =
      PolygonScaledReciprocal.reciprocal (-a)⁻¹ (Polynomial.toLaurent (l ty))
    rw [tensorShearDividedConicMap_y, map_mul, map_add, conicBoundarySecond_v,
      AlgHom.commutes, conicBoundarySecond_inverse_eq U₀ c₀ a ha hc,
      hy, map_mul, Polynomial.toLaurent_X, Polynomial.toLaurent_C,
      map_mul, PolygonScaledReciprocal.reciprocal_T, PolygonScaledReciprocal.reciprocal_C]
    congr 1
    exact (map_add LaurentPolynomial.C _ _).trans
      (congrArg (fun z => z + LaurentPolynomial.C r) (map_neg LaurentPolynomial.C _)) |>.symm

end FLT.Mazur.WeierstrassSuccessiveX
