/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearInitialSlopeProjections
public import FLT.Mazur.WeierstrassCoefficientShearScaleOneParameter

/-!
# Original Laurent functions across the full initial slope boundary

The actual initial and retained projections identify the ordered tangent
parameter on every Laurent function, preserving the original root shift.
-/

@[expose] public noncomputable section
open scoped TensorProduct LaurentPolynomial
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

local notation "L" => tensorShearScaleOneLaurentMap W (π ^ 0) d.b3 d.b4 d.b6
  S r hs hd3 hd4 hd6 hr

/-- The original initial Laurent parameter restricted through the actual tensor overlap. -/
def coefficientShearInitialBoundaryParameter : S[T;T⁻¹] →ₐ[S] O :=
  ((J).symm.toAlgHom.comp (IsScalarTower.toAlgHom S (S ⊗[R] I) _)).comp L

/-- The complete canonical boundary comparison preserves every original Laurent function. -/
theorem coefficientShearInitialBoundaryParameter_comparison
    (b : Sˣ) (hb : (b : S) = a) :
    (E).toAlgHom.comp
        (coefficientShearInitialBoundaryParameter d S r hr hd3 hd4 hd6) =
      (hb ▸ slopeLaurentMap b) := by
  apply AlgHom.ext
  intro w
  have H₀ := AlgHom.congr_fun
    (coefficientShearInitialSlopeBoundary_initial hπ d e S r hp h3 h4 hr hd3 hd4 hd6) (L w)
  change E ((J).symm (algebraMap (S ⊗[R] I) _ (L w))) = EI (L w) at H₀
  exact H₀.trans (AlgHom.congr_fun
    (tensorShearScaleOneLaurentMap_comparison W (π ^ 0) d.b3 d.b4 d.b6
      S r hs hd3 hd4 hd6 hr b hb) w)

/-- On the retained side, the actual transition has the identical whole Laurent parameter. -/
theorem coefficientShearInitialBoundaryParameter_retained
    (b : Sˣ) (hb : (b : S) = a) (w : S[T;T⁻¹]) :
    B (coefficientShearInitialBoundaryParameter d S r hr hd3 hd4 hd6 w) =
      (H).symm ((hb ▸ slopeLaurentMap b) w) := by
  apply (H).injective
  rw [AlgEquiv.apply_symm_apply]
  exact AlgHom.congr_fun
    (coefficientShearInitialBoundaryParameter_comparison
      hπ d e S r hp h3 h4 hr hd3 hd4 hd6 b hb) w

end FLT.Mazur.WeierstrassDividedDepth
