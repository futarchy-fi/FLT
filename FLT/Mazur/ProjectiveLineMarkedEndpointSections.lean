/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveLineMarkedHZero
/-!
# Intrinsic endpoint values of marked divisor sections

Evaluate actual pulled-back sections relative to the pulled-back canonical
section. At zero the coefficient is p(0)/(-a)^m; at infinity it is the top
coefficient of p. The canonical endpoint section cancels scalars, so these
are intrinsic values, not merely evaluations of chart polynomials. The H0
formulas use the existing bounded-polynomial equivalence.
-/

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open scoped Polynomial
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.ProjectiveLineMarkedEndpointSections
open FCurve PolygonDivisorNormalizationPullback
open ProjectiveLineMarkedCharts ProjectiveLineMarkedDualCoordinates
open ProjectiveLineMarkedPullbackCoordinates ProjectiveLineMarkedSectionTransition
open ProjectiveLineMarkedPolynomialBounds
variable (K : Type u) [Field K]
/-- The chart-origin pullback is polynomial evaluation at zero. -/
lemma chartZero_coordinate (p : K[X]) :
    (ProjectiveLine.chartZero K).appTop (coordinateRing K p) =
      (Scheme.ΓSpecIso (.of K)).inv (p.eval 0) := by
  exact (congrArg (fun k ↦ k.hom p) (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (Polynomial.evalRingHom 0)))).symm
/-- At the chart origin the powered divisor equation is (-b)^m. -/
lemma chartZero_equation_power (b : K) (m : ℕ) :
    (ProjectiveLine.chartZero K).appTop (equation K b ^ m) =
      (Scheme.ΓSpecIso (.of K)).inv ((-b) ^ m) := by
  rw [map_pow, equation, chartZero_coordinate]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, zero_sub, map_pow]
/-- The pulled-back canonical section cancels scalars away from the marked point. -/
lemma chart_canonical_cancel (a : Kˣ) (m : ℕ)
    (j : ProjectiveLine.chart K ⟶ ProjectiveLine.scheme K) [IsOpenImmersion j]
    (b : K) (hb : b ≠ 0) (hj : (markedPoint K a).ker.comap j = (chartPoint K b).ker) :
    Function.Injective (fun r : Γ(Spec (.of K), ⊤) ↦
      r • pullGlobal (ProjectiveLine.chartZero K ≫ j) (line K a m)
        (divisorSection ((relativeCartier K a).1.pow m) ⊤)) := by
  let I := (chartPoint K b).ker ^ m
  let hI := (effectiveCartier K b).pow m
  let x : I.ideal (chartTop K) := ⟨equation K b ^ m, by
    rw [show I.ideal (chartTop K) = Ideal.span {equation K b ^ m} from power_equation K b m]
    exact Ideal.subset_span (Set.mem_singleton _)⟩
  apply pullGlobal_chart_smul_cancel (ProjectiveLine.chartZero K) j (line K a m)
    (idealModule I) (chartPowerIso K a j b hj m) _ (divisorSection hI ⊤) _
    ((idealModuleAffineEquiv I (chartTop K)).symm x)
  · change IsRegular ((ProjectiveLine.chartZero K).appTop
      (divisorChartEval I (chartTop K) (divisorSection hI ⊤) x))
    rw [divisorSection_eval]
    change IsRegular ((ProjectiveLine.chartZero K).appTop (equation K b ^ m))
    rw [chartZero_equation_power]
    exact ((isUnit_iff_ne_zero.mpr (pow_ne_zero m (neg_ne_zero.mpr hb))).map
      (Scheme.ΓSpecIso (.of K)).inv.hom).isRegular
  · rw [divisorSection, pullGlobal_hom]
    exact divisorLinePullbackIsoOfEq_section_apply _ _ _ _ ⊤
/-- The chart coordinate relation holds in the actual endpoint pullback module. -/
lemma chart_endpoint_scaled (a : Kˣ) (m : ℕ)
    (j : ProjectiveLine.chart K ⟶ ProjectiveLine.scheme K) [IsOpenImmersion j]
    (b : K) (hj : (markedPoint K a).ker.comap j = (chartPoint K b).ker)
    (s : structureModule (ProjectiveLine.scheme K) ⟶ line K a m) :
    (Scheme.ΓSpecIso (.of K)).inv ((-b) ^ m) •
      pullGlobal (ProjectiveLine.chartZero K ≫ j) (line K a m)
        (s.app ⊤ (1 : Γ(ProjectiveLine.scheme K, ⊤))) =
    (Scheme.ΓSpecIso (.of K)).inv ((polynomial K a m j b hj s).eval 0) •
      pullGlobal (ProjectiveLine.chartZero K ≫ j) (line K a m)
        (divisorSection ((relativeCartier K a).1.pow m) ⊤) := by
  have he := pullGlobal_coordinate_relation (ProjectiveLine.chartZero K) j (line K a m)
    (chartSectionsCoordinate K a j b hj m)
    (divisorSection ((relativeCartier K a).1.pow m) ⊤)
    (s.app ⊤ (1 : Γ(ProjectiveLine.scheme K, ⊤)))
  rw [coordinate_canonical, ← polynomial_coordinate, chartZero_equation_power,
    chartZero_coordinate] at he
  exact he
/-- An endpoint section is its normalized polynomial value times the canonical section. -/
lemma chart_endpoint (a : Kˣ) (m : ℕ)
    (j : ProjectiveLine.chart K ⟶ ProjectiveLine.scheme K) [IsOpenImmersion j]
    (b : K) (hb : b ≠ 0) (hj : (markedPoint K a).ker.comap j = (chartPoint K b).ker)
    (s : structureModule (ProjectiveLine.scheme K) ⟶ line K a m) :
    pullGlobal (ProjectiveLine.chartZero K ≫ j) (line K a m)
        (s.app ⊤ (1 : Γ(ProjectiveLine.scheme K, ⊤))) =
    (Scheme.ΓSpecIso (.of K)).inv ((polynomial K a m j b hj s).eval 0 / (-b) ^ m) •
      pullGlobal (ProjectiveLine.chartZero K ≫ j) (line K a m)
        (divisorSection ((relativeCartier K a).1.pow m) ⊤) := by
  have he := congrArg (fun t ↦ (Scheme.ΓSpecIso (.of K)).inv (((-b) ^ m)⁻¹) • t)
    (chart_endpoint_scaled K a m j b hj s)
  simpa only [smul_smul, ← map_mul, inv_mul_cancel₀ (pow_ne_zero m (neg_ne_zero.mpr hb)),
    map_one, one_smul, ← div_eq_inv_mul] using he
/-- The intrinsic zero value is the constant polynomial coefficient divided by (-a)^m. -/
lemma zero_endpoint (a : Kˣ) (m : ℕ)
    (s : structureModule (ProjectiveLine.scheme K) ⟶ line K a m) :
    pullGlobal (ProjectiveLine.zero K) (line K a m)
        (s.app ⊤ (1 : Γ(ProjectiveLine.scheme K, ⊤))) =
    (Scheme.ΓSpecIso (.of K)).inv ((leftPolynomial K a m s).eval 0 / (-(a : K)) ^ m) •
      pullGlobal (ProjectiveLine.zero K) (line K a m)
        (divisorSection ((relativeCartier K a).1.pow m) ⊤) :=
  chart_endpoint K a m (ProjectiveLine.left K) a (Units.ne_zero a) (left_ideal K a) s
/-- The intrinsic infinity value is the degree-m polynomial coefficient. -/
lemma infinity_endpoint (a : Kˣ) (m : ℕ)
    (s : structureModule (ProjectiveLine.scheme K) ⟶ line K a m) :
    pullGlobal (ProjectiveLine.infinity K) (line K a m)
        (s.app ⊤ (1 : Γ(ProjectiveLine.scheme K, ⊤))) =
    (Scheme.ΓSpecIso (.of K)).inv ((leftPolynomial K a m s).coeff m) •
      pullGlobal (ProjectiveLine.infinity K) (line K a m)
        (divisorSection ((relativeCartier K a).1.pow m) ⊤) := by
  have he := chart_endpoint K a m (ProjectiveLine.right K) (a⁻¹ : Kˣ)
    (Units.ne_zero _) (right_ideal K a) s
  change _ = (Scheme.ΓSpecIso (.of K)).inv
    ((rightPolynomial K a m s).eval 0 / (-(↑a⁻¹ : K)) ^ m) • _ at he
  rw [rightPolynomial_endpoint_ratio] at he
  exact he
open ProjectiveLineMarkedHZero in
/-- The H0 polynomial equivalence computes the actual zero-endpoint section. -/
lemma zero_h0 (a : Kˣ) (m : ℕ) (x : H0 K a m) :
    pullGlobal (ProjectiveLine.zero K) (line K a m)
        (moduleScalarH0Equiv (ProjectiveLine.toBase K) (line K a m) x) =
    (Scheme.ΓSpecIso (.of K)).inv
        (((polynomialEquiv K a m x).val).eval 0 / (-(a : K)) ^ m) •
      pullGlobal (ProjectiveLine.zero K) (line K a m)
        (divisorSection ((relativeCartier K a).1.pow m) ⊤) := by
  have hp : (polynomialEquiv K a m x).val = leftPolynomial K a m
      (globalSectionHom (line K a m)
        (moduleScalarH0Equiv (ProjectiveLine.toBase K) (line K a m) x)) := rfl
  rw [hp]
  simpa only [globalSectionHom_top] using
    zero_endpoint K a m (globalSectionHom (line K a m)
      (moduleScalarH0Equiv (ProjectiveLine.toBase K) (line K a m) x))
open ProjectiveLineMarkedHZero in
/-- The H0 polynomial equivalence computes the actual infinity-endpoint section. -/
lemma infinity_h0 (a : Kˣ) (m : ℕ) (x : H0 K a m) :
    pullGlobal (ProjectiveLine.infinity K) (line K a m)
        (moduleScalarH0Equiv (ProjectiveLine.toBase K) (line K a m) x) =
    (Scheme.ΓSpecIso (.of K)).inv (((polynomialEquiv K a m x).val).coeff m) •
      pullGlobal (ProjectiveLine.infinity K) (line K a m)
        (divisorSection ((relativeCartier K a).1.pow m) ⊤) := by
  have hp : (polynomialEquiv K a m x).val = leftPolynomial K a m
      (globalSectionHom (line K a m)
        (moduleScalarH0Equiv (ProjectiveLine.toBase K) (line K a m) x)) := rfl
  rw [hp]
  simpa only [globalSectionHom_top] using
    infinity_endpoint K a m (globalSectionHom (line K a m)
      (moduleScalarH0Equiv (ProjectiveLine.toBase K) (line K a m) x))
end FLT.Mazur.ProjectiveLineMarkedEndpointSections
