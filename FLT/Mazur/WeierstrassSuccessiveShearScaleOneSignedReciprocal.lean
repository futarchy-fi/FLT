/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearScaleOneBoundaryCoordinates
public import FLT.Mazur.WeierstrassSuccessiveShearSignedReciprocal
public import FLT.Mazur.WeierstrassSuccessiveXConicPuncturedParameters
public import FLT.Mazur.PolygonScaledReciprocal

/-!
# Signed reciprocal comparison for the first scale-one conic

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
set_option maxRecDepth 2048
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (S : Type u) [CommRing S] [Algebra R S] (r : S)
  (hs : algebraMap R S s = 1) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S b3 = 0) (h4 : algebraMap R S b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "U₀" => rootShearCurve (W.map (algebraMap R S)) r
local notation "c₀" => algebraMap R S b6
local notation "T₀" => WeierstrassDilatation.ScalarExtension W (s * π) b3 b4 b6 S
local notation "tx" => WeierstrassDilatation.tensorX W (s * π) b3 b4 b6 S
local notation "ty" => WeierstrassDilatation.tensorY W (s * π) b3 b4 b6 S
local notation "φ" => tensorShearScaleOneDividedConicMap W s π b3 b4 b6 S r hs hp h3 h4 hr
variable (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
  (hc : algebraMap R S b6 = 0)
local notation "hu₀" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)

/-- Positive reciprocal agreement holds on every original divided tensor function. -/
theorem tensorShearScaleOneConicFirst_reciprocal
    (l : T₀ →ₐ[S] Polynomial S) (hx : l tx = Polynomial.X)
    (hy : l ty = Polynomial.X * Polynomial.C r) :
    (conicBoundaryFirst U₀ c₀ hu₀ hc).comp φ =
      (PolygonScaledReciprocal.reciprocal a⁻¹).comp (Polynomial.toLaurentAlg.comp l) := by
  apply Algebra.TensorProduct.ext_ring
  apply WeierstrassDilatation.hom_ext
  · change conicBoundaryFirst U₀ c₀ hu₀ hc (φ tx) =
      PolygonScaledReciprocal.reciprocal a⁻¹ (Polynomial.toLaurent (l tx))
    rw [tensorShearScaleOneDividedConicMap_x, conicBoundaryFirst_inverse_eq U₀ c₀ a ha hc,
      hx, Polynomial.toLaurent_X, PolygonScaledReciprocal.reciprocal_T]
  · change conicBoundaryFirst U₀ c₀ hu₀ hc (φ ty) =
      PolygonScaledReciprocal.reciprocal a⁻¹ (Polynomial.toLaurent (l ty))
    rw [tensorShearScaleOneDividedConicMap_y, map_mul, map_add, conicBoundaryFirst_v,
      AlgHom.commutes, zero_add, conicBoundaryFirst_inverse_eq U₀ c₀ a ha hc,
      hy, map_mul, Polynomial.toLaurent_X, Polynomial.toLaurent_C,
      map_mul, PolygonScaledReciprocal.reciprocal_T, PolygonScaledReciprocal.reciprocal_C]
    rfl

/-- Negative reciprocal agreement keeps the opposite original slope on the whole algebra. -/
theorem tensorShearScaleOneConicSecond_reciprocal
    (l : T₀ →ₐ[S] Polynomial S) (hx : l tx = Polynomial.X)
    (hy : l ty = Polynomial.X * Polynomial.C (-(U₀).a₁ + r)) :
    (conicBoundarySecond U₀ c₀ hu₀ hc).comp φ =
      (PolygonScaledReciprocal.reciprocal (-a)⁻¹).comp (Polynomial.toLaurentAlg.comp l) := by
  apply Algebra.TensorProduct.ext_ring
  apply WeierstrassDilatation.hom_ext
  · change conicBoundarySecond U₀ c₀ hu₀ hc (φ tx) =
      PolygonScaledReciprocal.reciprocal (-a)⁻¹ (Polynomial.toLaurent (l tx))
    rw [tensorShearScaleOneDividedConicMap_x, conicBoundarySecond_inverse_eq U₀ c₀ a ha hc,
      hx, Polynomial.toLaurent_X, PolygonScaledReciprocal.reciprocal_T]
  · change conicBoundarySecond U₀ c₀ hu₀ hc (φ ty) =
      PolygonScaledReciprocal.reciprocal (-a)⁻¹ (Polynomial.toLaurent (l ty))
    rw [tensorShearScaleOneDividedConicMap_y, map_mul, map_add, conicBoundarySecond_v,
      AlgHom.commutes, conicBoundarySecond_inverse_eq U₀ c₀ a ha hc,
      hy, map_mul, Polynomial.toLaurent_X, Polynomial.toLaurent_C,
      map_mul, PolygonScaledReciprocal.reciprocal_T, PolygonScaledReciprocal.reciprocal_C]
    congr 1
    exact (map_add LaurentPolynomial.C _ _).trans
      (congrArg (fun z => z + LaurentPolynomial.C r) (map_neg LaurentPolynomial.C _)) |>.symm

end FLT.Mazur.WeierstrassSuccessiveX
