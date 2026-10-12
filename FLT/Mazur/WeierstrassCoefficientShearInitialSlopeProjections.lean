/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearInitialSlopeBoundary
public import FLT.Mazur.WeierstrassCoefficientShearScaleOne

/-!
# Full canonical initial boundary projections after the tangent shear

The coordinate comparisons identify the complete algebra maps, preserving
all functions rather than only points of the two original tensor charts.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 2048
universe u
variable {R : Type u} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (d : Data W π 0) (e : Data W π (0 + 1))
  (S : Type u) [CommRing S] [Algebra R S] (r : S)
  (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S e.b3 = 0) (h4 : algebraMap R S e.b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "a" => WeierstrassCurve.a₁ (rootShearCurve (W.map (algebraMap R S)) r)
local notation "P" => SlopeOpen a
local notation "A" => WeierstrassDilatation.Coordinate W (π ^ 0) d.b3 d.b4 d.b6
local notation "T" => S ⊗[R] A
local notation "x" => WeierstrassDilatation.x W (π ^ 0) d.b3 d.b4 d.b6
local notation "y" => WeierstrassDilatation.y W (π ^ 0) d.b3 d.b4 d.b6
local notation "tx" => (1 : S) ⊗ₜ[R] x
local notation "O" => Localization.Away tx
local notation "u" => coord W (π ^ 0) π e.b3 e.b4 e.b6 2
local notation "hs" => (by simp : algebraMap R S (π ^ 0) = 1)
local notation "B" => PrincipalOpenTensor.transition S x u (previousBoundaryEquiv hπ d e)
local notation "H" => tensorShearScaleOneHorizontalEquiv W (π ^ 0) π
  e.b3 e.b4 e.b6 S r hs hp h3 h4 hr

local notation "E" => coefficientShearInitialSlopeBoundaryEquiv hπ d e S r hp h3 h4 hr
local notation "I" => WeierstrassModificationX.Coordinate W (π ^ 0) d.b3 d.b4 d.b6
local notation "t" => WeierstrassModificationX.t W (π ^ 0) d.b3 d.b4 d.b6
local notation "J" => PrincipalOpenTensor.transition S x t
  (overlapEquiv W (π ^ 0) d.b3 d.b4 d.b6)
variable (hd3 : algebraMap R S d.b3 = 0) (hd4 : algebraMap R S d.b4 = 0)
  (hd6 : algebraMap R S d.b6 = 0)
local notation "EI" => tensorShearScaleOneEquiv W (π ^ 0) d.b3 d.b4 d.b6
  S r hs hd3 hd4 hd6 hr

/-- The initial projection is the complete canonical slope comparison. -/
theorem coefficientShearInitialSlopeBoundary_initial :
    (E).toAlgHom.comp ((J).symm.toAlgHom.comp
      (IsScalarTower.toAlgHom S (S ⊗[R] I) _)) = (EI).toAlgHom := by
  apply Algebra.TensorProduct.ext_ring
  apply WeierstrassModificationX.hom_ext
  · change E ((J).symm (algebraMap (S ⊗[R] I) _ ((1 : S) ⊗ₜ[R] t))) = EI ((1 : S) ⊗ₜ[R] t)
    rw [coefficientShearInitialSlopeBoundary_t, tensorShearScaleOneEquiv_t]
  · change E ((J).symm (algebraMap (S ⊗[R] I) _
      ((1 : S) ⊗ₜ[R] WeierstrassModificationX.v W (π ^ 0) d.b3 d.b4 d.b6))) =
        EI ((1 : S) ⊗ₜ[R] WeierstrassModificationX.v W (π ^ 0) d.b3 d.b4 d.b6)
    rw [coefficientShearInitialSlopeBoundary_v, tensorShearScaleOneEquiv_v]

/-- The retained projection is the complete canonical horizontal localization comparison. -/
theorem coefficientShearInitialSlopeBoundary_retained
    (z : Localization.Away ((1 : S) ⊗ₜ[R] u)) : E ((B).symm z) = H z := by
  change H (B ((B).symm z)) = H z
  rw [AlgEquiv.apply_symm_apply]

end FLT.Mazur.WeierstrassDividedDepth
