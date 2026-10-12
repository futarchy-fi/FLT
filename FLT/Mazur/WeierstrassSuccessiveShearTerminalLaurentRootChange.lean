/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearTerminalLaurentConic
public import FLT.Mazur.WeierstrassSuccessiveShearTerminalBranchRootChange
public import FLT.Mazur.PolygonScaledReciprocal

/-!
# Companion-root exchange on the entire terminal Laurent algebra

The actual original tensor functions force the scaled reciprocal T ↦ c/T.
The divided constant is retained, rather than inferred from endpoint markings.
-/

@[expose] public noncomputable section
open scoped TensorProduct LaurentPolynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassDividedDepth WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (π : R)
  (k : ℕ) (b3 b4 b6 : R) (S : Type u) [CommRing S] [Algebra R S] (r : S)
  (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S b3 = 0) (h4 : algebraMap R S b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "D" => S ⊗[R] WeierstrassDilatation.Coordinate W (π ^ (k + 1)) b3 b4 b6
local notation "x" => WeierstrassDilatation.x W (π ^ (k + 1)) b3 b4 b6
local notation "y" => WeierstrassDilatation.y W (π ^ (k + 1)) b3 b4 b6
variable (hc : IsUnit (algebraMap R S b6))
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
  (t : S) (ht : t ^ 2 + algebraMap R S W.a₁ * t - algebraMap R S W.a₂ = 0)
  (b : Sˣ) (hb : (b : S) = (rootShearCurve (W.map (algebraMap R S)) t).a₁)
  (hrt : r + t = -algebraMap R S W.a₁)
local notation "E" => tensorShearTerminalLaurentEquiv W π k b3 b4 b6 S r hp h3 h4 hr hc a ha
local notation "F" => tensorShearTerminalLaurentEquiv W π k b3 b4 b6 S t hp h3 h4 ht hc b hb
local notation "c" => algebraMap R S b6
local notation "q" => PolygonScaledReciprocal.reciprocal hc.unit
open LaurentPolynomial
include hrt

/-- The full original tensor normalization exchanges roots by the actual scaled reciprocal. -/
theorem tensorShearTerminalLaurentEquiv_rootChange :
    (E).toAlgHom = (q).comp (F).toAlgHom := by
  have hab : a = -b := terminalShearUnits_rootChange W S r a ha t b hb hrt
  have hi : (↑b⁻¹ : S) = -(↑a⁻¹ : S) := by
    rw [hab]
    simp only [Units.val_neg, inv_neg, neg_neg]
  have Hc : C c * C (↑hc.unit⁻¹ : S) = (1 : S[T;T⁻¹]) := by
    simpa only [map_mul, map_one, hc.unit_spec] using congrArg C (Units.mul_inv hc.unit)
  have Hrt : (C r - C t) * C (↑a⁻¹ : S) = (1 : S[T;T⁻¹]) := by
    rw [← map_sub, terminalShearRoot_difference W S r a ha t hrt,
      ← map_mul, Units.mul_inv, map_one]
  have Hx : q (F ((1 : S) ⊗ₜ[R] x)) = E ((1 : S) ⊗ₜ[R] x) := by
    rw [tensorShearTerminalLaurent_x, tensorShearTerminalLaurent_x,
      map_mul, map_sub, map_mul, PolygonScaledReciprocal.reciprocal_C,
      PolygonScaledReciprocal.reciprocal_C, PolygonScaledReciprocal.reciprocal_T,
      PolygonScaledReciprocal.reciprocal_T_inv, hc.unit_spec, hi, map_neg]
    linear_combination -C (↑a⁻¹ : S) * T 1 * Hc
  apply Algebra.TensorProduct.ext_ring
  apply WeierstrassDilatation.hom_ext
  · exact Hx.symm
  · change E ((1 : S) ⊗ₜ[R] y) = q (F ((1 : S) ⊗ₜ[R] y))
    rw [tensorShearTerminalLaurent_y, tensorShearTerminalLaurent_y]
    rw [map_add, map_mul, PolygonScaledReciprocal.reciprocal_T,
      PolygonScaledReciprocal.reciprocal_C, hc.unit_spec]
    rw [← tensorShearTerminalLaurent_x W π k b3 b4 b6 S t hp h3 h4 ht hc b hb,
      Hx, tensorShearTerminalLaurent_x]
    linear_combination (C c * T (-1) - T 1) * Hrt

end FLT.Mazur.WeierstrassSuccessiveX
