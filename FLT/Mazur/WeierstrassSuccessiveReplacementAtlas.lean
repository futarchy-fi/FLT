/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveReplacementGluing

/-!
# Three actual charts of the successive whole modification

The unchanged exterior, the new x-direction chart and the deeper divided
chart form an actual open cover. The contraction retains the original
projective cubic, and the new charts have their proved local contractions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.WeierstrassSuccessiveX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π c3 c4 c6 : R)

/-- Every replacement point belongs to the unchanged exterior or the actual new local step. -/
theorem replacement_charts_cover (z : replacement W s π c3 c4 c6) :
    (∃ a, replacementExterior W s π c3 c4 c6 a = z) ∨
      ∃ a, replacementInner W s π c3 c4 c6 a = z := by
  obtain ⟨i, a, ha⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective
    (span (WeierstrassModificationX.xOpenInclusion W s (π * c3) (π * c4) (π ^ 2 * c6))
      (replacementOverlap W s π c3 c4 c6)) z
  cases i with
  | none =>
    left
    refine ⟨WeierstrassModificationX.xOpenInclusion W s
      (π * c3) (π * c4) (π ^ 2 * c6) a, ?_⟩
    change (WeierstrassModificationX.xOpenInclusion W s (π * c3) (π * c4) (π ^ 2 * c6) ≫
      replacementExterior W s π c3 c4 c6) a = z
    rw [show WeierstrassModificationX.xOpenInclusion W s (π * c3) (π * c4) (π ^ 2 * c6) ≫
      replacementExterior W s π c3 c4 c6 = colimit.ι
        (span (WeierstrassModificationX.xOpenInclusion W s
          (π * c3) (π * c4) (π ^ 2 * c6)) (replacementOverlap W s π c3 c4 c6))
        WalkingSpan.zero from colimit.w
          (span (WeierstrassModificationX.xOpenInclusion W s
            (π * c3) (π * c4) (π ^ 2 * c6)) (replacementOverlap W s π c3 c4 c6))
          WalkingSpan.Hom.fst]
    exact ha
  | some i =>
    cases i with
    | left => exact Or.inl ⟨a, ha⟩
    | right => exact Or.inr ⟨a, ha⟩

/-- The actual new x-direction chart inside the whole replacement. -/
def replacementXChart : Spec (.of (Coordinate W s π c3 c4 c6)) ⟶
    replacement W s π c3 c4 c6 :=
  xChart W s π c3 c4 c6 ≫ replacementInner W s π c3 c4 c6

/-- The actual deeper divided chart inside the whole replacement. -/
def replacementDividedChart : Spec (.of
    (WeierstrassDilatation.Coordinate W (s * π) c3 c4 c6)) ⟶ replacement W s π c3 c4 c6 :=
  dividedChart W s π c3 c4 c6 ≫ replacementInner W s π c3 c4 c6

instance replacementXChart_isOpenImmersion :
    IsOpenImmersion (replacementXChart W s π c3 c4 c6) := by
  unfold replacementXChart
  infer_instance

instance replacementDividedChart_isOpenImmersion :
    IsOpenImmersion (replacementDividedChart W s π c3 c4 c6) := by
  unfold replacementDividedChart
  infer_instance

/-- The exterior and both actual new affine charts cover the whole replacement. -/
theorem replacement_three_charts_cover (z : replacement W s π c3 c4 c6) :
    (∃ a, replacementExterior W s π c3 c4 c6 a = z) ∨
      (∃ a, replacementXChart W s π c3 c4 c6 a = z) ∨
        ∃ a, replacementDividedChart W s π c3 c4 c6 a = z := by
  rcases replacement_charts_cover W s π c3 c4 c6 z with h | ⟨a, rfl⟩
  · exact Or.inl h
  · rcases modification_charts_cover W s π c3 c4 c6 a with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · exact Or.inr (Or.inl ⟨b, rfl⟩)
    · exact Or.inr (Or.inr ⟨b, rfl⟩)

/-- The new x-chart's whole contraction retains its preceding divided coordinates. -/
@[reassoc] theorem replacementXChart_contraction :
    replacementXChart W s π c3 c4 c6 ≫ replacementContraction W s π c3 c4 c6 =
      toDivided W s π c3 c4 c6 ≫
        WeierstrassModificationX.dividedChart W s (π * c3) (π * c4) (π ^ 2 * c6) := by
  simp only [replacementXChart, Category.assoc, replacementInner_contraction,
    xChart_contraction_assoc]

/-- The new divided chart contracts by the actual refinement map. -/
@[reassoc] theorem replacementDividedChart_contraction :
    replacementDividedChart W s π c3 c4 c6 ≫ replacementContraction W s π c3 c4 c6 =
      dividedToPrevious W s π c3 c4 c6 ≫
        WeierstrassModificationX.dividedChart W s (π * c3) (π * c4) (π ^ 2 * c6) := by
  simp only [replacementDividedChart, Category.assoc, replacementInner_contraction,
    dividedChart_contraction_assoc]

/-- The replacement retains contraction to the same original projective cubic. -/
def replacementToCurve (h3 : W.a₃ = s * (π * c3)) (h4 : W.a₄ = s * (π * c4))
    (h6 : W.a₆ = s ^ 2 * (π ^ 2 * c6)) :
    replacement W s π c3 c4 c6 ⟶ WeierstrassIntegralChart.integralCurve W :=
  replacementContraction W s π c3 c4 c6 ≫
    WeierstrassModificationX.contraction W s (π * c3) (π * c4) (π ^ 2 * c6) h3 h4 h6

/-- The inner local step has the same original projective contraction after replacement. -/
@[reassoc] theorem replacementInner_toCurve
    (h3 : W.a₃ = s * (π * c3)) (h4 : W.a₄ = s * (π * c4))
    (h6 : W.a₆ = s ^ 2 * (π ^ 2 * c6)) :
    replacementInner W s π c3 c4 c6 ≫ replacementToCurve W s π c3 c4 c6 h3 h4 h6 =
      contractionToCurve W s π c3 c4 c6 h3 h4 h6 := by
  simp only [replacementToCurve, replacementInner_contraction_assoc,
    WeierstrassModificationX.dividedChart_contraction, contractionToCurve]

end FLT.Mazur.WeierstrassSuccessiveX
