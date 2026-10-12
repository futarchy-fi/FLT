/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearInitialLineBoundary
public import FLT.Mazur.WeierstrassIncidenceShearConicCoefficient
public import FLT.Mazur.WeierstrassSuccessiveXConicPunctureCompatibility
/-!
# Both arbitrary-root initial conic punctures are the original reciprocal boundaries

Compare every tensor function through the actual two integral transitions.
The second tangent retains its negative scale and original root-shifted slope.
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
variable (g3 : algebraMap R S d.b3 = 0) (g4 : algebraMap R S d.b4 = 0)
  (g6 : algebraMap R S d.b6 = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "U" => rootShearCurve (W.map (algebraMap R S)) r
local notation "c" => algebraMap R S d.b6
local notation "F" => tensorShearInitialConicMap W (π ^ k) d.b3 d.b4 d.b6 S r hs g3 g4 hr
local notation "P₁" => conicPuncturedFirst U c g6
local notation "P₂" => conicPuncturedSecond U c g6
local notation "L₁" => coefficientShearInitialLineBoundaryMap hπ d e S r hs hp h3 h4 hr
  0 (middle_first_root U) a⁻¹
local notation "L₂" => coefficientShearInitialLineBoundaryMap hπ d e S r hs hp h3 h4 hr
  (-(U).a₁) (middle_second_root U) (-a)⁻¹

include ha in
/-- Every original initial tensor function has the first root's signed reciprocal restriction. -/
theorem coefficientShearInitialFirstLine_algebra :
    (L₁).comp (Algebra.algHom S A Q) = (P₁).comp F := by
  apply Algebra.TensorProduct.ext_ring
  apply WeierstrassModificationX.hom_ext
  · simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
      Algebra.TensorProduct.includeRight_apply]
    refine (coefficientShearInitialLineBoundaryMap_t
      hπ d e S r hs hp h3 h4 hr 0 (middle_first_root U) a⁻¹).trans ?_
    erw [inv_inv, ha, tensorShearInitialConicMap_t]
    exact (conicEvaluation_t ..).symm
  · simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
      Algebra.TensorProduct.includeRight_apply]
    refine (coefficientShearInitialLineBoundaryMap_v
      hπ d e S r hs hp h3 h4 hr 0 (middle_first_root U) a⁻¹).trans ?_
    erw [zero_add, tensorShearInitialConicMap_v, map_add, AlgHom.commutes]
    rw [conicPuncturedFirst, conicEvaluation_v, zero_add]
    rfl

include ha in
/-- The opposite root keeps its negative reciprocal and the unsheared original slope. -/
theorem coefficientShearInitialSecondLine_algebra :
    (L₂).comp (Algebra.algHom S A Q) = (P₂).comp F := by
  apply Algebra.TensorProduct.ext_ring
  apply WeierstrassModificationX.hom_ext
  · simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
      Algebra.TensorProduct.includeRight_apply]
    refine (coefficientShearInitialLineBoundaryMap_t
      hπ d e S r hs hp h3 h4 hr (-(U).a₁) (middle_second_root U) (-a)⁻¹).trans ?_
    erw [inv_inv, Units.val_neg, ha, tensorShearInitialConicMap_t, map_neg]
    exact (conicEvaluation_t ..).symm
  · simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
      Algebra.TensorProduct.includeRight_apply]
    refine (coefficientShearInitialLineBoundaryMap_v
      hπ d e S r hs hp h3 h4 hr (-(U).a₁) (middle_second_root U) (-a)⁻¹).trans ?_
    erw [tensorShearInitialConicMap_v]
    simp only [map_add, AlgHom.commutes, conicPuncturedSecond, conicEvaluation_v, map_neg]
    rfl

end FLT.Mazur.WeierstrassDividedDepth
