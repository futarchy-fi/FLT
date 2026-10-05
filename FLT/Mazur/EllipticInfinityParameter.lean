/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticReductionKernel

/-!
# An injective local parameter on actual E₁ points

The infinity chart has a unique maximal-ideal s-coordinate for each t-coordinate.
Primitive projective coordinates give the chart [-X/Y : -1 : -Z/Y], so t is an
injective parameter on actual points reducing to infinity. This statement needs
neither completeness nor a formal power-series evaluation assumption.
-/

@[expose] public section

namespace FLT.Mazur
open IsLocalRing WeierstrassCurve WeierstrassCurve.Projective

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)

/-- The actual local Weierstrass equation in the integral infinity chart. -/
def InfinityChartEquation (t s : A) : Prop :=
  s = t ^ 3 + W.a₁ * t * s + W.a₂ * t ^ 2 * s + W.a₃ * s ^ 2 +
    W.a₄ * t * s ^ 2 + W.a₆ * s ^ 3

/-- For fixed t in the maximal ideal, the maximal-ideal s-coordinate is unique. -/
theorem infinityChart_unique {t s₁ s₂ : A} (ht : t ∈ maximalIdeal A)
    (hs₁ : s₁ ∈ maximalIdeal A) (hs₂ : s₂ ∈ maximalIdeal A)
    (h₁ : InfinityChartEquation A W t s₁) (h₂ : InfinityChartEquation A W t s₂) :
    s₁ = s₂ := by
  have ht0 := (residue_eq_zero_iff _).mpr ht
  have hs₁0 := (residue_eq_zero_iff _).mpr hs₁
  have hs₂0 := (residue_eq_zero_iff _).mpr hs₂
  let d := 1 - W.a₁ * t - W.a₂ * t ^ 2 - W.a₃ * (s₁ + s₂) -
    W.a₄ * t * (s₁ + s₂) - W.a₆ * (s₁ ^ 2 + s₁ * s₂ + s₂ ^ 2)
  have hd : IsUnit d := (residue_ne_zero_iff_isUnit _).mp (by simp [d, ht0, hs₁0, hs₂0])
  apply sub_eq_zero.mp
  apply hd.mul_right_eq_zero.mp
  dsimp only [d]
  unfold InfinityChartEquation at h₁ h₂
  linear_combination h₁ - h₂

/-- In the maximal-ideal chart, s is t³ times an integral unit. -/
theorem infinityChart_eq_cube_mul_unit {t s : A} (ht : t ∈ maximalIdeal A)
    (hs : s ∈ maximalIdeal A) (he : InfinityChartEquation A W t s) :
    ∃ u : Aˣ, s = t ^ 3 * u ∧ residue A (u : A) = 1 := by
  have ht0 := (residue_eq_zero_iff _).mpr ht
  have hs0 := (residue_eq_zero_iff _).mpr hs
  let d := 1 - W.a₁ * t - W.a₂ * t ^ 2 - W.a₃ * s - W.a₄ * t * s - W.a₆ * s ^ 2
  have hd0 : residue A d = 1 := by simp [d, ht0, hs0]
  have hd : IsUnit d := (residue_ne_zero_iff_isUnit _).mp (hd0 ▸ one_ne_zero)
  have hmul : s * d = t ^ 3 := by
    dsimp only [d]
    unfold InfinityChartEquation at he
    linear_combination he
  refine ⟨hd.unit⁻¹, ?_, ?_⟩
  · have hdv : d * (↑hd.unit⁻¹ : A) = 1 := by
      simpa only [hd.unit_spec] using hd.unit.mul_inv
    rw [← hmul, mul_assoc, hdv, mul_one]
  · rw [map_units_inv, hd.unit_spec, hd0, inv_one]

/-- Primitive coordinates normalize to [t : -1 : s] in the infinity chart. -/
theorem primitiveLift_infinity_chart {P : (W.map (algebraMap A K)).toProjective.Point}
    (v : PrimitiveLift A P.point) (hP : InfinityReduction A W P) (t s : A)
    (ht : (t : K) = -(v.coords 0 : K) / (v.coords 1 : K))
    (hs : (s : K) = -(v.coords 2 : K) / (v.coords 1 : K)) :
    P.point = ⟦![(t : K), -1, (s : K)]⟧ := by
  have hy : (v.coords 1 : K) ≠ 0 :=
    fun he => (v.isUnit_y A W hP).ne_zero (Subtype.ext he)
  rw [← v.represents]
  apply Quotient.sound
  have hv : (fun i => (v.coords i : K)) = -(v.coords 1 : K) • ![(t : K), -1, (s : K)] := by
    ext i
    fin_cases i <;> simp [ht, hs] <;> field_simp
  rw [hv]
  exact smul_equiv _ (Ne.isUnit (neg_ne_zero.mpr hy))

/-- Each E₁ point admits maximal-ideal coordinates in the normalized infinity chart. -/
theorem exists_ellipticE1_chart (P : ellipticE1 A W) :
    ∃ t s : A, t ∈ maximalIdeal A ∧ s ∈ maximalIdeal A ∧ InfinityChartEquation A W t s ∧
      P.val.point = ⟦![(t : K), -1, (s : K)]⟧ := by
  let v := primitiveLift A W P.val
  obtain ⟨t, s, ht, hs, ht0, hs0, he⟩ := ellipticE1_exists_parameters A W P v
  exact ⟨t, s, ht0, hs0, he, primitiveLift_infinity_chart A W v P.property t s ht hs⟩

/-- The local parameter t = -X/Y on actual E₁ points. -/
noncomputable def infinityParameter (P : ellipticE1 A W) : A :=
  (exists_ellipticE1_chart A W P).choose

/-- The parameter belongs to the maximal ideal. -/
theorem infinityParameter_mem (P : ellipticE1 A W) :
    infinityParameter A W P ∈ maximalIdeal A :=
  (exists_ellipticE1_chart A W P).choose_spec.choose_spec.1

/-- The local parameter distinguishes actual E₁ points. -/
theorem infinityParameter_injective : Function.Injective (infinityParameter A W) := by
  intro P Q ht
  obtain ⟨s₁, ht₁, hs₁, he₁, hp⟩ := (exists_ellipticE1_chart A W P).choose_spec
  obtain ⟨s₂, ht₂, hs₂, he₂, hq⟩ := (exists_ellipticE1_chart A W Q).choose_spec
  change infinityParameter A W P ∈ _ at ht₁
  change InfinityChartEquation A W (infinityParameter A W P) s₁ at he₁
  change InfinityChartEquation A W (infinityParameter A W Q) s₂ at he₂
  have hs : s₁ = s₂ := infinityChart_unique A W ht₁ hs₁ hs₂ he₁ (ht ▸ he₂)
  apply Subtype.ext
  apply Point.ext
  rw [hp, hq]
  change (⟦![(infinityParameter A W P : K), -1, (s₁ : K)]⟧ : PointClass K) =
    ⟦![(infinityParameter A W Q : K), -1, (s₂ : K)]⟧
  rw [ht, hs]

/-- The identity has parameter zero. -/
@[simp] theorem infinityParameter_zero : infinityParameter A W 0 = 0 := by
  obtain ⟨s, _, _, _, hp⟩ := (exists_ellipticE1_chart A W 0).choose_spec
  change (⟦![0, 1, 0]⟧ : PointClass K) =
    ⟦![(infinityParameter A W 0 : K), -1, (s : K)]⟧ at hp
  obtain ⟨u, hu⟩ := Quotient.exact hp
  apply Subtype.ext
  simpa [Units.smul_def, eq_comm] using congrFun hu 0

/-- Vanishing of the parameter characterizes the identity. -/
@[simp] theorem infinityParameter_eq_zero_iff (P : ellipticE1 A W) :
    infinityParameter A W P = 0 ↔ P = 0 := by
  rw [← infinityParameter_zero A W]
  exact (infinityParameter_injective A W).eq_iff

end FLT.Mazur
