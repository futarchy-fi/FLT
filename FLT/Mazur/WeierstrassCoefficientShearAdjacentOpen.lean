/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearAdjacentLine

/-!
# Signed adjacent-line comparison on the entire horizontal localization

Extend the actual adjacent line contraction by inverting the original divided
horizontal function. Both conic punctures agree on this whole localization.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
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
local notation "T₀" => WeierstrassDilatation.ScalarExtension W (π ^ k * π) d.b3 d.b4 d.b6 S
local notation "x₀" => WeierstrassDilatation.tensorX W (π ^ k * π) d.b3 d.b4 d.b6 S
local notation "O" => TensorDividedOpen W (π ^ k) π d.b3 d.b4 d.b6 S
local notation "U" => rootShearCurve (W.map (algebraMap R S)) r
variable (v : S) (hv : v * (v + (rootShearCurve (W.map (algebraMap R S)) r).a₁) = 0)
local notation "l" => coefficientShearAdjacentLine hπ d e S r hp h3 h4 hr v hv

/-- The actual adjacent line contraction extended over its whole horizontal open. -/
def coefficientShearAdjacentOpen : O →ₐ[S] S[T;T⁻¹] :=
  IsLocalization.Away.liftAlgHom x₀ (f := Polynomial.toLaurentAlg.comp l) (by
    change IsUnit (Polynomial.toLaurent (l x₀))
    rw [coefficientShearAdjacentLine_x, Polynomial.toLaurent_X]
    exact LaurentPolynomial.isUnit_T 1)

/-- The localized contraction retains every original divided tensor function. -/
theorem coefficientShearAdjacentOpen_base (z : T₀) :
    coefficientShearAdjacentOpen hπ d e S r hp h3 h4 hr v hv (algebraMap T₀ O z) =
      Polynomial.toLaurent (l z) := by
  rw [coefficientShearAdjacentOpen, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

local notation "g3" => And.left (coefficientShearAdjacent_coefficients hπ d e S hp)
local notation "g4" => And.left (And.right (coefficientShearAdjacent_coefficients hπ d e S hp))
local notation "gc" => And.right (And.right (coefficientShearAdjacent_coefficients hπ d e S hp))
local notation "c" => algebraMap R S d.b6
local notation "φ" => tensorShearDividedConicOpenEquiv W (π ^ k) π
  d.b3 d.b4 d.b6 S r hs hp g3 g4 hr
variable (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "l₁" => coefficientShearAdjacentOpen hπ d e S r hp h3 h4 hr
  0 (middle_first_root U)
local notation "l₂" => coefficientShearAdjacentOpen hπ d e S r hp h3 h4 hr
  (-WeierstrassCurve.a₁ U) (middle_second_root U)

/-- The positive signed reciprocal equality holds on the complete localization. -/
theorem coefficientShearAdjacentFirst_open_reciprocal :
    (conicBoundaryFirst U c hu gc).comp (φ).toAlgHom =
      (PolygonScaledReciprocal.reciprocal a⁻¹).comp l₁ := by
  apply IsLocalization.algHom_ext (Submonoid.powers x₀)
  apply AlgHom.ext
  intro z
  change conicBoundaryFirst U c hu gc (φ (algebraMap T₀ O z)) =
    PolygonScaledReciprocal.reciprocal a⁻¹ (l₁ (algebraMap T₀ O z))
  rw [coefficientShearAdjacentOpen_base]
  exact DFunLike.congr_fun
    (coefficientShearAdjacentFirst_reciprocal hπ d e S r hs hp h3 h4 hr a ha) z

/-- The negative signed reciprocal equality also holds on every localized function. -/
theorem coefficientShearAdjacentSecond_open_reciprocal :
    (conicBoundarySecond U c hu gc).comp (φ).toAlgHom =
      (PolygonScaledReciprocal.reciprocal (-a)⁻¹).comp l₂ := by
  apply IsLocalization.algHom_ext (Submonoid.powers x₀)
  apply AlgHom.ext
  intro z
  change conicBoundarySecond U c hu gc (φ (algebraMap T₀ O z)) =
    PolygonScaledReciprocal.reciprocal (-a)⁻¹ (l₂ (algebraMap T₀ O z))
  rw [coefficientShearAdjacentOpen_base]
  exact DFunLike.congr_fun
    (coefficientShearAdjacentSecond_reciprocal hπ d e S r hs hp h3 h4 hr a ha) z

end FLT.Mazur.WeierstrassDividedDepth
