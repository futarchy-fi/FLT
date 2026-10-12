/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearAdjacentTransition
public import FLT.Mazur.WeierstrassSuccessiveShearScaleOneSignedReciprocal

/-!
# Both signed attachments from the first scale-one retained conic

The original next line contractions agree on every divided tensor function
and every localized function, through the genuine corrected adjacent transition.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k : ℕ}
  (d : Data W π (k + 1)) (e : Data W π (k + 1 + 1))
  (S : Type u) [CommRing S] [Algebra R S] (r : S)
  (hs : algebraMap R S (π ^ k) = 1) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S e.b3 = 0) (h4 : algebraMap R S e.b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "U" => rootShearCurve (W.map (algebraMap R S)) r
local notation "c" => algebraMap R S d.b6
local notation "g3" => And.left (coefficientShearAdjacent_coefficients hπ d e S hp)
local notation "g4" => And.left (And.right (coefficientShearAdjacent_coefficients hπ d e S hp))
local notation "gc" => And.right (And.right (coefficientShearAdjacent_coefficients hπ d e S hp))
local notation "φ" => tensorShearScaleOneDividedConicMap W (π ^ k) π
  d.b3 d.b4 d.b6 S r hs hp g3 g4 hr
variable (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "l₁" => coefficientShearAdjacentLine hπ d e S r hp h3 h4 hr
  0 (middle_first_root U)
local notation "l₂" => coefficientShearAdjacentLine hπ d e S r hp h3 h4 hr
  (-WeierstrassCurve.a₁ U) (middle_second_root U)

/-- Every original divided function agrees with the actual next first line at a⁻¹/z. -/
theorem coefficientShearScaleOneAdjacentFirst_reciprocal :
    (conicBoundaryFirst U c hu gc).comp φ =
      (PolygonScaledReciprocal.reciprocal a⁻¹).comp (Polynomial.toLaurentAlg.comp l₁) := by
  apply tensorShearScaleOneConicFirst_reciprocal W (π ^ k) π d.b3 d.b4 d.b6 S r
    hs hp g3 g4 hr a ha gc l₁
  · exact coefficientShearAdjacentLine_x hπ d e S r hp h3 h4 hr 0 (middle_first_root U)
  · simpa only [zero_add] using
      coefficientShearAdjacentLine_y hπ d e S r hp h3 h4 hr 0 (middle_first_root U)

/-- The actual next opposite line agrees at -a⁻¹/z, including its original slope. -/
theorem coefficientShearScaleOneAdjacentSecond_reciprocal :
    (conicBoundarySecond U c hu gc).comp φ =
      (PolygonScaledReciprocal.reciprocal (-a)⁻¹).comp (Polynomial.toLaurentAlg.comp l₂) := by
  apply tensorShearScaleOneConicSecond_reciprocal W (π ^ k) π d.b3 d.b4 d.b6 S r
    hs hp g3 g4 hr a ha gc l₂
  · exact coefficientShearAdjacentLine_x hπ d e S r hp h3 h4 hr
      (-WeierstrassCurve.a₁ U) (middle_second_root U)
  · exact coefficientShearAdjacentLine_y hπ d e S r hp h3 h4 hr
      (-WeierstrassCurve.a₁ U) (middle_second_root U)


local notation "T₀" => WeierstrassDilatation.ScalarExtension W (π ^ k * π) d.b3 d.b4 d.b6 S
local notation "x₀" => WeierstrassDilatation.tensorX W (π ^ k * π) d.b3 d.b4 d.b6 S
local notation "O" => TensorDividedOpen W (π ^ k) π d.b3 d.b4 d.b6 S
local notation "Φ" => tensorShearScaleOneDividedConicOpenEquiv W (π ^ k) π
  d.b3 d.b4 d.b6 S r hs hp g3 g4 hr
local notation "E" => tensorAdjacentBoundaryEquiv hπ d e S
local notation "hsNext" => coefficientShearAdjacent_scale S hp (k := k)
local notation "L₁" => tensorShearLineOpenMap W (π ^ (k + 1)) π
  e.b3 e.b4 e.b6 S r hsNext hp h3 h4 hr 0 (middle_first_root U)
local notation "L₂" => tensorShearLineOpenMap W (π ^ (k + 1)) π
  e.b3 e.b4 e.b6 S r hsNext hp h3 h4 hr (-WeierstrassCurve.a₁ U) (middle_second_root U)

/-- The entire first conic puncture factors through the actual next horizontal transition. -/
theorem coefficientShearScaleOneAdjacentFirst_transition :
    (conicBoundaryFirst U c hu gc).comp (Φ).toAlgHom =
      ((PolygonScaledReciprocal.reciprocal a⁻¹).comp L₁).comp (E).toAlgHom := by
  rw [AlgHom.comp_assoc, coefficientShearAdjacentOpen_transition]
  apply IsLocalization.algHom_ext (Submonoid.powers x₀)
  apply AlgHom.ext
  intro z
  change conicBoundaryFirst U c hu gc (Φ (algebraMap T₀ O z)) =
    PolygonScaledReciprocal.reciprocal a⁻¹
      (coefficientShearAdjacentOpen hπ d e S r hp h3 h4 hr
        0 (middle_first_root U) (algebraMap T₀ O z))
  rw [coefficientShearAdjacentOpen_base]
  exact AlgHom.congr_fun
    (coefficientShearScaleOneAdjacentFirst_reciprocal hπ d e S r hs hp h3 h4 hr a ha) z

/-- The whole opposite puncture uses the same genuine transition and negative reciprocal. -/
theorem coefficientShearScaleOneAdjacentSecond_transition :
    (conicBoundarySecond U c hu gc).comp (Φ).toAlgHom =
      ((PolygonScaledReciprocal.reciprocal (-a)⁻¹).comp L₂).comp (E).toAlgHom := by
  rw [AlgHom.comp_assoc, coefficientShearAdjacentOpen_transition]
  apply IsLocalization.algHom_ext (Submonoid.powers x₀)
  apply AlgHom.ext
  intro z
  change conicBoundarySecond U c hu gc (Φ (algebraMap T₀ O z)) =
    PolygonScaledReciprocal.reciprocal (-a)⁻¹
      (coefficientShearAdjacentOpen hπ d e S r hp h3 h4 hr
        (-WeierstrassCurve.a₁ U) (middle_second_root U) (algebraMap T₀ O z))
  rw [coefficientShearAdjacentOpen_base]
  exact AlgHom.congr_fun
    (coefficientShearScaleOneAdjacentSecond_reciprocal hπ d e S r hs hp h3 h4 hr a ha) z

end FLT.Mazur.WeierstrassDividedDepth
