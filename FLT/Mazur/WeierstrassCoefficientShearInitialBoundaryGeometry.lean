/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearInitialConicBoundaryAlgebra
public import FLT.Mazur.PrincipalOpenTensorGeometry
public import FLT.Mazur.WeierstrassDividedFiniteLineReciprocals
/-!
# Actual initial conic boundaries for arbitrary tangent roots

Both full Laurent punctures follow the original tensor transitions and the
canonical horizontal line lift with their ordered signed reciprocal scales.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory
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
local notation "u₀" => coord W (π ^ k) π e.b3 e.b4 e.b6 2
local notation "B" => PrincipalOpenTensor.transitionIso S x u₀ (previousBoundaryEquiv hπ d e)
local notation "J" => PrincipalOpenTensor.transitionIso S x t₀
  (overlapEquiv W (π ^ k) d.b3 d.b4 d.b6)
local notation "H" => tensorShearLineToHorizontal W (π ^ k) π
  e.b3 e.b4 e.b6 S r hs hp h3 h4 hr

/-- The algebra restriction is exactly the canonical full line lift and original transitions. -/
theorem coefficientShearInitialLineBoundary_spec
    (v : S) (hv : v * (v + (rootShearCurve (W.map (algebraMap R S)) r).a₁) = 0)
    (scale : Sˣ) :
    Spec.map (CommRingCat.ofHom
      (coefficientShearInitialLineBoundaryMap hπ d e S r hs hp h3 h4 hr v hv scale).toRingHom) =
      Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.reciprocal scale).toRingHom) ≫
        H v hv ≫ (B).hom ≫ (J).inv := by
  rw [coefficientShearInitialLineBoundaryMap, lineSpec_comp, lineSpec_comp,
    coefficientShearFiniteLineBoundaryMap, lineSpec_comp, tensorShearLineOpenMap_spec]
  simp only [Category.assoc]
  rfl

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
/-- The first conic puncture has the actual positive reciprocal tensor overlap. -/
@[reassoc] theorem coefficientShearInitialFirstLine_boundary_spec :
    Spec.map (CommRingCat.ofHom (P₁).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (F).toRingHom) =
      Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.reciprocal a⁻¹).toRingHom) ≫
        H 0 (middle_first_root U) ≫ (B).hom ≫ (J).inv ≫
          PrincipalOpenTensor.inclusion S t₀ := by
  have h := congrArg (fun f => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f)))
    (coefficientShearInitialFirstLine_algebra hπ d e S r hs hp h3 h4 hr g3 g4 g6 a ha)
  rw [lineSpec_comp, lineSpec_comp, coefficientShearInitialLineBoundary_spec] at h
  simp only [Category.assoc] at h
  convert h.symm using 1 <;> rfl

include ha in
/-- The opposite conic puncture keeps the negative reciprocal and root-shifted slope. -/
@[reassoc] theorem coefficientShearInitialSecondLine_boundary_spec :
    Spec.map (CommRingCat.ofHom (P₂).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (F).toRingHom) =
      Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.reciprocal (-a)⁻¹).toRingHom) ≫
        H (-(U).a₁) (middle_second_root U) ≫ (B).hom ≫ (J).inv ≫
          PrincipalOpenTensor.inclusion S t₀ := by
  have h := congrArg (fun f => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f)))
    (coefficientShearInitialSecondLine_algebra hπ d e S r hs hp h3 h4 hr g3 g4 g6 a ha)
  rw [lineSpec_comp, lineSpec_comp, coefficientShearInitialLineBoundary_spec] at h
  simp only [Category.assoc] at h
  convert h.symm using 1 <;> rfl

end FLT.Mazur.WeierstrassDividedDepth
