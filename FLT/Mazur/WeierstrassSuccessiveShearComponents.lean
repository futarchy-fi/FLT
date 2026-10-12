/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearNormalForm
public import FLT.Mazur.WeierstrassSuccessiveXMiddleUnion
public import FLT.Mazur.WeierstrassSuccessiveXTensorContraction

/-!
# Original functions on the coefficient-split retained components

The full conic and both horizontal lines detect every original tensor function.
The original contraction retains x=u and y=u*(v+r), so the horizontal parameter
and the two unsheared slopes are explicit, including at their node origins.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassDividedDepth WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (S : Type u) [CommRing S] [Algebra R S] (r : S)
local notation "q" => algebraMap R S
local notation "U" => rootShearCurve (W.map q) r
local notation "a" => WeierstrassCurve.a₁ U
local notation "c" => q b6
variable (hs : algebraMap R S s = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S b3 = 0) (h4 : algebraMap R S b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "h2" => coefficientShear_a₂_zero W S r hr
local notation "e" => tensorShearMiddleEquiv W s π b3 b4 b6 S r hs hp h3 h4
local notation "T" => ScalarExtension W s π b3 b4 b6 S

/-- Restrict original tensor functions to the whole exceptional conic. -/
def tensorShearConicMap : T →ₐ[S] ConicCoordinate a c :=
  (middleConicMap U c h2).comp (e).toAlgHom

/-- Restrict original tensor functions to the entire line of the chosen split slope. -/
def tensorShearLineMap (v : S) (hv : v * (v + a) = 0) : T →ₐ[S] S[X] :=
  (middleLineMap U c h2 v hv).comp (e).toAlgHom

/-- The original conic restriction keeps incidence and the original root-shifted slope. -/
theorem tensorShearConicMap_coord (i : Fin 3) :
    tensorShearConicMap W s π b3 b4 b6 S r hs hp h3 h4 hr
      (tensorCoord W s π b3 b4 b6 S i) =
        ![conicT a c, conicV a c + algebraMap S _ r, 0] i := by
  change middleConicMap U c h2 ((e) (tensorCoord W s π b3 b4 b6 S i)) = _
  rw [tensorShearMiddleEquiv_coord]
  fin_cases i <;> simp [middleConicMap_coord]

/-- The free horizontal parameter survives, and the original slope is v+r. -/
theorem tensorShearLineMap_coord (v : S) (hv : v * (v + a) = 0) (i : Fin 3) :
    tensorShearLineMap W s π b3 b4 b6 S r hs hp h3 h4 hr v hv
      (tensorCoord W s π b3 b4 b6 S i) = ![0, C (v + r), X] i := by
  change middleLineMap U c h2 v hv ((e) (tensorCoord W s π b3 b4 b6 S i)) = _
  rw [tensorShearMiddleEquiv_coord]
  fin_cases i <;> simp [middleLineMap_coord]

/-- The original preceding x is the whole polynomial parameter of either tangent line. -/
theorem tensorShearLineMap_previous_x (v : S) (hv : v * (v + a) = 0) :
    tensorShearLineMap W s π b3 b4 b6 S r hs hp h3 h4 hr v hv
      (tensorPreviousMap W s π b3 b4 b6 S
        (WeierstrassDilatation.x W s (π * b3) (π * b4) (π ^ 2 * b6))) = X := by
  rw [tensorPreviousMap_x, tensorShearLineMap_coord]
  rfl

/-- The original preceding y has the true unsheared slope, with no cancellation of x. -/
theorem tensorShearLineMap_previous_y (v : S) (hv : v * (v + a) = 0) :
    tensorShearLineMap W s π b3 b4 b6 S r hs hp h3 h4 hr v hv
      (tensorPreviousMap W s π b3 b4 b6 S
        (WeierstrassDilatation.y W s (π * b3) (π * b4) (π ^ 2 * b6))) = X * C (v + r) := by
  rw [tensorPreviousMap_y, map_mul, tensorShearLineMap_coord, tensorShearLineMap_coord]
  rfl

/-- The conic and both ordered full lines detect every original tensor function. -/
theorem tensorShear_components_detect_zero (ha : IsUnit a) (z : T)
    (hc : tensorShearConicMap W s π b3 b4 b6 S r hs hp h3 h4 hr z = 0)
    (h0 : tensorShearLineMap W s π b3 b4 b6 S r hs hp h3 h4 hr
      0 (middle_first_root U) z = 0)
    (h1 : tensorShearLineMap W s π b3 b4 b6 S r hs hp h3 h4 hr
      (-a) (middle_second_root U) z = 0) : z = 0 := by
  apply (e).injective
  rw [map_zero]
  exact middle_components_detect_zero U c h2 ha ((e) z) hc h0 h1

/-- Agreement on the actual conic and ordered lines is scheme-theoretic equality. -/
theorem tensorShear_components_ext (ha : IsUnit a) (x y : T)
    (hc : tensorShearConicMap W s π b3 b4 b6 S r hs hp h3 h4 hr x =
      tensorShearConicMap W s π b3 b4 b6 S r hs hp h3 h4 hr y)
    (h0 : tensorShearLineMap W s π b3 b4 b6 S r hs hp h3 h4 hr
      0 (middle_first_root U) x =
      tensorShearLineMap W s π b3 b4 b6 S r hs hp h3 h4 hr 0 (middle_first_root U) y)
    (h1 : tensorShearLineMap W s π b3 b4 b6 S r hs hp h3 h4 hr
      (-a) (middle_second_root U) x =
      tensorShearLineMap W s π b3 b4 b6 S r hs hp h3 h4 hr (-a) (middle_second_root U) y) :
    x = y := by
  apply sub_eq_zero.mp
  apply tensorShear_components_detect_zero W s π b3 b4 b6 S r hs hp h3 h4 hr ha
  · rw [map_sub, hc, sub_self]
  · rw [map_sub, h0, sub_self]
  · rw [map_sub, h1, sub_self]

end FLT.Mazur.WeierstrassSuccessiveX
