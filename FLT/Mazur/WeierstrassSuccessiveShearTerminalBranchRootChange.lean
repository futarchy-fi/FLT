/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearTerminalBranchCoordinates
public import FLT.Mazur.WeierstrassDilatationShearNodeNormalForm
public import FLT.Mazur.NodalFiberNodeComparison

/-!
# Companion-root exchange on both complete terminal branches

The original tensor functions identify opposite branches with the same full
polynomial parameter. Their affine origins are retained in the comparison.
-/

@[expose] public noncomputable section
open scoped TensorProduct
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
variable (h6 : algebraMap R S b6 = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "E" => tensorShearTerminalNodeEquiv W π k b3 b4 b6 S r hp h3 h4 hr h6 a ha
open Polynomial

variable (t : S)
  (ht : t ^ 2 + algebraMap R S W.a₁ * t - algebraMap R S W.a₂ = 0)
  (b : Sˣ) (hb : (b : S) = (rootShearCurve (W.map (algebraMap R S)) t).a₁)
  (hrt : r + t = -algebraMap R S W.a₁)
include ha hb hrt

/-- Companion tangent roots reverse the invertible tangent difference. -/
theorem terminalShearUnits_rootChange : a = -b := by
  apply Units.ext
  rw [Units.val_neg, ha, hb]
  rw [(rootShearCurve_coefficients (W := W.map (algebraMap R S)) r).1,
    (rootShearCurve_coefficients (W := W.map (algebraMap R S)) t).1]
  change algebraMap R S W.a₁ + 2 * r = -(algebraMap R S W.a₁ + 2 * t)
  linear_combination 2 * hrt

omit hb in
/-- The root difference is the original invertible tangent difference. -/
theorem terminalShearRoot_difference : r - t = (a : S) := by
  rw [ha, (rootShearCurve_coefficients (W := W.map (algebraMap R S)) r).1]
  change r - t = algebraMap R S W.a₁ + 2 * r
  linear_combination -hrt

/-- The first complete tensor branch becomes the opposite branch at the companion root. -/
theorem tensorShearTerminalFirstMap_rootChange :
    tensorShearTerminalFirstMap W π k b3 b4 b6 S r hp h3 h4 hr h6 a ha =
      tensorShearTerminalSecondMap W π k b3 b4 b6 S t hp h3 h4 ht h6 b hb := by
  have hab : a = -b := terminalShearUnits_rootChange W S r a ha t b hb hrt
  have hi : (↑b⁻¹ : S) = -(↑a⁻¹ : S) := by
    rw [hab]
    simp only [Units.val_neg, inv_neg, neg_neg]
  have H : (C r - C t) * C (↑a⁻¹ : S) = (1 : S[X]) := by
    rw [← map_sub, terminalShearRoot_difference W S r a ha t hrt,
      ← map_mul, Units.mul_inv, map_one]
  apply Algebra.TensorProduct.ext_ring
  apply WeierstrassDilatation.hom_ext
  · change tensorShearTerminalFirstMap W π k b3 b4 b6 S r hp h3 h4 hr h6 a ha
      ((1 : S) ⊗ₜ[R] x) =
        tensorShearTerminalSecondMap W π k b3 b4 b6 S t hp h3 h4 ht h6 b hb
          ((1 : S) ⊗ₜ[R] x)
    rw [tensorShearTerminalFirstMap_x, tensorShearTerminalSecondMap_x, hi, map_neg]
  · change tensorShearTerminalFirstMap W π k b3 b4 b6 S r hp h3 h4 hr h6 a ha
      ((1 : S) ⊗ₜ[R] y) =
        tensorShearTerminalSecondMap W π k b3 b4 b6 S t hp h3 h4 ht h6 b hb
          ((1 : S) ⊗ₜ[R] y)
    rw [tensorShearTerminalFirstMap_y, tensorShearTerminalSecondMap_y, hi, map_neg]
    linear_combination -X * H

/-- The opposite complete tensor branch becomes the first branch with the same parameter. -/
theorem tensorShearTerminalSecondMap_rootChange :
    tensorShearTerminalSecondMap W π k b3 b4 b6 S r hp h3 h4 hr h6 a ha =
      tensorShearTerminalFirstMap W π k b3 b4 b6 S t hp h3 h4 ht h6 b hb := by
  exact (tensorShearTerminalFirstMap_rootChange W π k b3 b4 b6 S t hp h3 h4 ht h6 b hb
    r hr a ha (by rw [add_comm]; exact hrt)).symm

end FLT.Mazur.WeierstrassSuccessiveX
