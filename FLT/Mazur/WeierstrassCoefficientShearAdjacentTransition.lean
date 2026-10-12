/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearAdjacentOpen
public import FLT.Mazur.WeierstrassDividedAdjacentBoundaryAlgebra
public import FLT.Mazur.WeierstrassSuccessiveShearLineOpen

/-!
# Actual adjacent-line restriction through the original horizontal transition

The localized adjacent contraction is the restriction to the entire next line,
composed with base change of the genuine integral preceding-boundary transition.
Both signed conic comparisons therefore use that actual transition.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k : ℕ}
  (d : Data W π (k + 1)) (e : Data W π (k + 1 + 1))
  (S : Type u) [CommRing S] [Algebra R S] (r : S)
  (hs : algebraMap R S (π ^ k) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S e.b3 = 0) (h4 : algebraMap R S e.b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "U" => rootShearCurve (W.map (algebraMap R S)) r
local notation "hsNext" => coefficientShearAdjacent_scale S hp (k := k)
local notation "x₀" => WeierstrassDilatation.tensorX W (π ^ k * π) d.b3 d.b4 d.b6 S
local notation "T₀" => WeierstrassDilatation.ScalarExtension W (π ^ k * π) d.b3 d.b4 d.b6 S
local notation "O" => TensorDividedOpen W (π ^ k) π d.b3 d.b4 d.b6 S
local notation "E" => tensorAdjacentBoundaryEquiv hπ d e S
variable (v : S) (hv : v * (v + (rootShearCurve (W.map (algebraMap R S)) r).a₁) = 0)
local notation "l" => tensorShearLineOpenMap W (π ^ (k + 1)) π
  e.b3 e.b4 e.b6 S r hsNext hp h3 h4 hr v hv

/-- The whole localized line map factors through the genuine preceding-boundary transition. -/
theorem coefficientShearAdjacentOpen_transition :
    (l).comp (E).toAlgHom = coefficientShearAdjacentOpen hπ d e S r hp h3 h4 hr v hv := by
  apply IsLocalization.algHom_ext (Submonoid.powers x₀)
  apply Algebra.TensorProduct.ext_ring
  apply AlgHom.ext
  intro z
  change l (E (algebraMap T₀ O ((1 : S) ⊗ₜ[R] z))) =
    coefficientShearAdjacentOpen hπ d e S r hp h3 h4 hr v hv
      (algebraMap T₀ O ((1 : S) ⊗ₜ[R] z))
  rw [tensorAdjacentBoundaryEquiv_base, tensorShearLineOpenMap_base,
    coefficientShearAdjacentOpen_base]
  change Polynomial.toLaurent _ = Polynomial.toLaurent ((1 : S) • _)
  rw [one_smul]
  rfl

local notation "g3" => And.left (coefficientShearAdjacent_coefficients hπ d e S hp)
local notation "g4" => And.left (And.right (coefficientShearAdjacent_coefficients hπ d e S hp))
local notation "gc" => And.right (And.right (coefficientShearAdjacent_coefficients hπ d e S hp))
local notation "c" => algebraMap R S d.b6
local notation "φ" => tensorShearDividedConicOpenEquiv W (π ^ k) π
  d.b3 d.b4 d.b6 S r hs hp g3 g4 hr
variable (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "l₁" => tensorShearLineOpenMap W (π ^ (k + 1)) π
  e.b3 e.b4 e.b6 S r hsNext hp h3 h4 hr 0 (middle_first_root U)
local notation "l₂" => tensorShearLineOpenMap W (π ^ (k + 1)) π
  e.b3 e.b4 e.b6 S r hsNext hp h3 h4 hr
  (-WeierstrassCurve.a₁ U) (middle_second_root U)

/-- The first conic puncture attaches by the true full transition and positive reciprocal. -/
theorem coefficientShearAdjacentFirst_transition :
    (conicBoundaryFirst U c hu gc).comp (φ).toAlgHom =
      ((PolygonScaledReciprocal.reciprocal a⁻¹).comp l₁).comp (E).toAlgHom := by
  rw [AlgHom.comp_assoc, coefficientShearAdjacentOpen_transition]
  exact coefficientShearAdjacentFirst_open_reciprocal hπ d e S r hs hp h3 h4 hr a ha

/-- The opposite puncture attaches by the same full transition and negative reciprocal. -/
theorem coefficientShearAdjacentSecond_transition :
    (conicBoundarySecond U c hu gc).comp (φ).toAlgHom =
      ((PolygonScaledReciprocal.reciprocal (-a)⁻¹).comp l₂).comp (E).toAlgHom := by
  rw [AlgHom.comp_assoc, coefficientShearAdjacentOpen_transition]
  exact coefficientShearAdjacentSecond_open_reciprocal hπ d e S r hs hp h3 h4 hr a ha

end FLT.Mazur.WeierstrassDividedDepth
