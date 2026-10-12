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
# Coefficient specialization of complete original terminal branches

Both original integral coordinate maps commute with polynomial coefficient
extension when the selected tangent root and its invertible difference do.
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

variable (T : Type u) [CommRing T] [Algebra R T] (f : S →ₐ[R] T) (t : T)
  (gp : algebraMap R T π = 0) (g3 : algebraMap R T b3 = 0)
  (g4 : algebraMap R T b4 = 0) (g6 : algebraMap R T b6 = 0)
  (ht : t ^ 2 + algebraMap R T W.a₁ * t - algebraMap R T W.a₂ = 0)
  (b : Tˣ) (hb : (b : T) = (rootShearCurve (W.map (algebraMap R T)) t).a₁)
  (hrt : f r = t)
include ha hb hrt

/-- Coefficient extension preserves the actual invertible tangent difference. -/
theorem terminalShearUnits_coefficient : Units.map f.toRingHom a = b := by
  apply Units.ext
  change f (a : S) = (b : T)
  rw [ha, hb]
  rw [(rootShearCurve_coefficients (W := W.map (algebraMap R S)) r).1,
    (rootShearCurve_coefficients (W := W.map (algebraMap R T)) t).1]
  change f (algebraMap R S W.a₁ + 2 * r) = algebraMap R T W.a₁ + 2 * t
  simp only [map_add, map_mul, map_ofNat, f.commutes, hrt]

/-- The complete first original branch specializes, including the node origin. -/
theorem originalShearTerminalFirstMap_coefficient :
    (Polynomial.mapAlgHom f).comp
        (originalShearTerminalFirstMap W π k b3 b4 b6 S r hp h3 h4 hr h6 a ha) =
      originalShearTerminalFirstMap W π k b3 b4 b6 T t gp g3 g4 ht g6 b hb := by
  have hi : f (↑a⁻¹ : S) = (↑b⁻¹ : T) := by
    have H := congrArg (fun u : Tˣ => (↑u⁻¹ : T))
      (terminalShearUnits_coefficient W S r a ha T f t b hb hrt)
    exact H
  apply WeierstrassDilatation.hom_ext
  · simp only [AlgHom.comp_apply, originalShearTerminalFirstMap_x,
      Polynomial.coe_mapAlgHom, map_mul, map_neg, Polynomial.map_C,
      Polynomial.map_X, AlgHom.coe_toRingHom, hi]
  · simp only [AlgHom.comp_apply, originalShearTerminalFirstMap_y,
      Polynomial.coe_mapAlgHom, map_add, map_mul, map_neg, Polynomial.map_C,
      Polynomial.map_X, AlgHom.coe_toRingHom, hi, hrt]

/-- The complete second original branch specializes, including the node origin. -/
theorem originalShearTerminalSecondMap_coefficient :
    (Polynomial.mapAlgHom f).comp
        (originalShearTerminalSecondMap W π k b3 b4 b6 S r hp h3 h4 hr h6 a ha) =
      originalShearTerminalSecondMap W π k b3 b4 b6 T t gp g3 g4 ht g6 b hb := by
  have hi : f (↑a⁻¹ : S) = (↑b⁻¹ : T) := by
    have H := congrArg (fun u : Tˣ => (↑u⁻¹ : T))
      (terminalShearUnits_coefficient W S r a ha T f t b hb hrt)
    exact H
  apply WeierstrassDilatation.hom_ext
  · simp only [AlgHom.comp_apply, originalShearTerminalSecondMap_x,
      Polynomial.coe_mapAlgHom, map_mul, Polynomial.map_C,
      Polynomial.map_X, AlgHom.coe_toRingHom, hi]
  · simp only [AlgHom.comp_apply, originalShearTerminalSecondMap_y,
      Polynomial.coe_mapAlgHom, map_mul, Polynomial.map_C,
      Polynomial.map_X, AlgHom.coe_toRingHom, hi, hrt]

end FLT.Mazur.WeierstrassSuccessiveX
