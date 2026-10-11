/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.BlowupFractionChartRatio

/-!
# Actual maps between Rees fraction charts

An ideal-preserving coefficient map sends A[I/f] to B[J/φ(f)]. The map is
constructed inside the original localizations, retains every generator ratio,
and works over rings with zero divisors. No exceptional locus is removed.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.BlowupFractionChart

set_option backward.isDefEq.respectTransparency false

variable {A B : Type*} [CommRing A] [CommRing B]
  (I : Ideal A) (J : Ideal B) (φ : A →+* B) (hφ : I.map φ ≤ J) (f : A)

/-- The localization map keeps the original coefficient homomorphism. -/
theorem fractionMap_base (a : A) :
    Localization.awayMap φ f (algebraMap A (Localization.Away f) a) =
      algebraMap B (Localization.Away (φ f)) (φ a) :=
  IsLocalization.map_eq _ _

/-- The original inverse denominator maps to the inverse of its actual image. -/
theorem fractionMap_inverse :
    Localization.awayMap φ f (IsLocalization.Away.invSelf f) =
      IsLocalization.Away.invSelf (φ f) := by
  apply (IsLocalization.Away.algebraMap_isUnit (φ f)
    (S := Localization.Away (φ f))).mul_left_cancel
  rw [← fractionMap_base φ f f, ← map_mul, IsLocalization.Away.mul_invSelf, map_one,
    fractionMap_base, IsLocalization.Away.mul_invSelf]

include hφ in
/-- Ideal preservation puts every original fraction-chart element in the target fraction chart. -/
theorem fractionMap_mem (z : Localization.Away f) (hz : z ∈ chart I f) :
    Localization.awayMap φ f z ∈ chart J (φ f) := by
  rw [chart_eq_adjoin] at hz
  induction hz using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨a, ha, rfl⟩ := hz
    rw [map_mul, fractionMap_base, fractionMap_inverse]
    exact (ratio J (φ f) (φ a) (hφ (Ideal.mem_map_of_mem φ ha))).property
  | algebraMap a =>
    rw [fractionMap_base]
    exact (chart J (φ f)).algebraMap_mem (φ a)
  | add x y hx hy ih ih' =>
    rw [map_add]
    exact (chart J (φ f)).add_mem ih ih'
  | mul x y hx hy ih ih' =>
    rw [map_mul]
    exact (chart J (φ f)).mul_mem ih ih'

/-- The actual ring homomorphism on the original Rees fraction algebras. -/
def chartMap : chart I f →+* chart J (φ f) :=
  ((Localization.awayMap φ f).comp (chart I f).val.toRingHom).codRestrict
    (chart J (φ f)).toSubring (fun z => fractionMap_mem I J φ hφ f z z.property)

/-- The constructed chart map is the restriction of the actual localization map. -/
theorem chartMap_val (z : chart I f) :
    (chartMap I J φ hφ f z : Localization.Away (φ f)) =
      Localization.awayMap φ f z := rfl

/-- Contraction of the chart map is exactly the original coefficient map. -/
@[simp] theorem chartMap_base (a : A) :
    chartMap I J φ hφ f (algebraMap A (chart I f) a) =
      algebraMap B (chart J (φ f)) (φ a) := by
  apply Subtype.ext
  exact fractionMap_base φ f a

/-- Every center-generator ratio retains its actual numerator and denominator. -/
@[simp] theorem chartMap_ratio (a : A) (ha : a ∈ I) :
    chartMap I J φ hφ f (ratio I f a ha) =
      ratio J (φ f) (φ a) (hφ (Ideal.mem_map_of_mem φ ha)) := by
  apply Subtype.ext
  change Localization.awayMap φ f
    (algebraMap A (Localization.Away f) a * IsLocalization.Away.invSelf f) = _
  rw [map_mul, fractionMap_base, fractionMap_inverse]
  rfl

/-- The image denominator is still the actual denominator in the target fraction chart. -/
@[simp] theorem chartMap_denominator :
    chartMap I J φ hφ f (denominator I f) = denominator J (φ f) :=
  chartMap_base I J φ hφ f f

end FLT.Mazur.BlowupFractionChart
