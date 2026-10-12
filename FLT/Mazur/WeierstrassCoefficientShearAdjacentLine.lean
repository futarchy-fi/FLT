/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearFiniteLineContraction
public import FLT.Mazur.WeierstrassSuccessiveShearSignedReciprocal

/-!
# Actual adjacent lines with the two signed conic reciprocals

Correct the scale of the genuine next line contraction by the original power
identity. Its full tensor map then equals the corresponding punctured conic
map, with the positive and negative inverse tangent scales kept separately.
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
  (hs : algebraMap R S (π ^ k) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S e.b3 = 0) (h4 : algebraMap R S e.b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "T" => WeierstrassDilatation.ScalarExtension W (π ^ k * π) d.b3 d.b4 d.b6 S
local notation "A" => WeierstrassDilatation.Coordinate W (π ^ k * π) d.b3 d.b4 d.b6
local notation "p" => WeierstrassDilatation.parameterEquiv W (π ^ k * π) (π ^ (k + 1))
  d.b3 d.b4 d.b6 d.b3 d.b4 d.b6 (Eq.symm (pow_succ π k)) rfl rfl rfl
omit [IsDomain R] in
include hp in
/-- The next original scale also vanishes over the chosen coefficient algebra. -/
theorem coefficientShearAdjacent_scale : algebraMap R S (π ^ (k + 1)) = 0 := by
  rw [pow_succ, map_mul, hp, mul_zero]
local notation "hsNext" => coefficientShearAdjacent_scale S hp (k := k)
variable (v : S) (hv : v * (v + (rootShearCurve (W.map (algebraMap R S)) r).a₁) = 0)
local notation "l" => coefficientShearFiniteLineContraction hπ d e S r hsNext hp h3 h4 hr v hv
local notation "tx" => WeierstrassDilatation.tensorX W (π ^ k * π) d.b3 d.b4 d.b6 S
local notation "ty" => WeierstrassDilatation.tensorY W (π ^ k * π) d.b3 d.b4 d.b6 S

/-- The genuine next line contraction on the actual next divided tensor equation. -/
def coefficientShearAdjacentLine : T →ₐ[S] S[X] :=
  AlgHom.liftEquiv R S _ _ ((l).comp (p).toAlgHom)

/-- The original next horizontal function is exactly the line parameter. -/
theorem coefficientShearAdjacentLine_x :
    coefficientShearAdjacentLine hπ d e S r hp h3 h4 hr v hv tx = X := by
  change (1 : S) • l (p _) = _
  rw [WeierstrassDilatation.parameterEquiv_x]
  exact tensorShearFiniteLineContraction_x hπ d e S r hsNext hp h3 h4 hr v hv

/-- The original next vertical function keeps the unsheared tangent slope. -/
theorem coefficientShearAdjacentLine_y :
    coefficientShearAdjacentLine hπ d e S r hp h3 h4 hr v hv ty = X * C (v + r) := by
  change (1 : S) • l (p _) = _
  rw [WeierstrassDilatation.parameterEquiv_y]
  exact tensorShearFiniteLineContraction_y hπ d e S r hsNext hp h3 h4 hr v hv

local notation "U" => rootShearCurve (W.map (algebraMap R S)) r
local notation "c" => algebraMap R S d.b6
include hπ hp e in
/-- The preceding divided coefficients vanish because the next depth exists. -/
theorem coefficientShearAdjacent_coefficients :
    algebraMap R S d.b3 = 0 ∧ algebraMap R S d.b4 = 0 ∧ algebraMap R S d.b6 = 0 := by
  constructor
  · rw [factor3_step hπ d e, map_mul, hp, zero_mul]
  constructor
  · rw [factor4_step hπ d e, map_mul, hp, zero_mul]
  · rw [factor6_step hπ d e, map_mul, map_pow, hp, zero_pow (by decide : 2 ≠ 0), zero_mul]
local notation "g3" => And.left (coefficientShearAdjacent_coefficients hπ d e S hp)
local notation "g4" => And.left (And.right (coefficientShearAdjacent_coefficients hπ d e S hp))
local notation "gc" => And.right (And.right (coefficientShearAdjacent_coefficients hπ d e S hp))
local notation "φ" => tensorShearDividedConicMap W (π ^ k) π
  d.b3 d.b4 d.b6 S r hs hp g3 g4 hr
variable (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "l₁" => coefficientShearAdjacentLine hπ d e S r hp h3 h4 hr
  0 (middle_first_root U)
local notation "l₂" => coefficientShearAdjacentLine hπ d e S r hp h3 h4 hr
  (-WeierstrassCurve.a₁ U) (middle_second_root U)

/-- Every original divided function agrees with the actual next first line at a⁻¹/z. -/
theorem coefficientShearAdjacentFirst_reciprocal :
    (conicBoundaryFirst U c hu gc).comp φ =
      (PolygonScaledReciprocal.reciprocal a⁻¹).comp (Polynomial.toLaurentAlg.comp l₁) := by
  apply tensorShearConicFirst_reciprocal W (π ^ k) π d.b3 d.b4 d.b6 S r
    hs hp g3 g4 hr a ha gc l₁
  · exact coefficientShearAdjacentLine_x hπ d e S r hp h3 h4 hr 0 (middle_first_root U)
  · simpa only [zero_add] using
      coefficientShearAdjacentLine_y hπ d e S r hp h3 h4 hr 0 (middle_first_root U)

/-- The actual next opposite line agrees at -a⁻¹/z, including its original slope. -/
theorem coefficientShearAdjacentSecond_reciprocal :
    (conicBoundarySecond U c hu gc).comp φ =
      (PolygonScaledReciprocal.reciprocal (-a)⁻¹).comp (Polynomial.toLaurentAlg.comp l₂) := by
  apply tensorShearConicSecond_reciprocal W (π ^ k) π d.b3 d.b4 d.b6 S r
    hs hp g3 g4 hr a ha gc l₂
  · exact coefficientShearAdjacentLine_x hπ d e S r hp h3 h4 hr
      (-(U).a₁) (middle_second_root U)
  · exact coefficientShearAdjacentLine_y hπ d e S r hp h3 h4 hr
      (-(U).a₁) (middle_second_root U)

end FLT.Mazur.WeierstrassDividedDepth
