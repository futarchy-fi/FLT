/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLocalAdditionCurveComparison
public import FLT.Mazur.WeierstrassInputAdditionCovers

/-!
# Gluing addition on the complete Y-chart input product

All six local laws agree on their actual intersections, including the full
infinity/affine intersection. They descend to one regular curve-valued map.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- The refined affine inclusion is the original transported-domain map. -/
theorem yProductAdditionCover_affine_f (i : AdditionChartIndex) :
    (yProductAdditionCover W hΔ).f ⟨.affine, i⟩ =
      transportedPolynomialDomainMap W 1 1 i hΔ := rfl

/-- The singleton polynomial refinement leaves its original domain inclusion unchanged. -/
theorem yProductAdditionCover_polynomial_f (i : PUnit) :
    (yProductAdditionCover W hΔ).f ⟨.polynomial, i⟩ =
      projectiveAdditionInclusion W 1 1 2 := by
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

/-- The singleton infinity refinement retains the original infinity inclusion. -/
theorem yProductAdditionCover_infinity_f (i : PUnit) :
    (yProductAdditionCover W hΔ).f ⟨.infinity, i⟩ = infinityAdditionInclusion W := by
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

/-- Each member of the six-member cover takes values in the same integral curve. -/
def yProductCurveLocal (i : (yProductAdditionCover W hΔ).I₀) :
    (yProductAdditionCover W hΔ).X i ⟶ integralCurve W :=
  yProductAdditionSpec W hΔ i ≫ integralCurveChart W (yProductAdditionOutput W hΔ i)

/-- The local laws agree on every scheme with the same Y-chart inputs. -/
theorem yProductCurveLocal_commonScheme (i j : (yProductAdditionCover W hΔ).I₀)
    {X : Scheme.{u}} (f : X ⟶ (yProductAdditionCover W hΔ).X i)
    (g : X ⟶ (yProductAdditionCover W hΔ).X j)
    (h : f ≫ (yProductAdditionCover W hΔ).f i =
      g ≫ (yProductAdditionCover W hΔ).f j) :
    f ≫ yProductCurveLocal W hΔ i = g ≫ yProductCurveLocal W hΔ j := by
  rcases i with ⟨i, a⟩
  rcases j with ⟨j, b⟩
  cases i <;> cases j <;>
    simp only [yProductAdditionCover_affine_f, yProductAdditionCover_polynomial_f,
      yProductAdditionCover_infinity_f] at h
  · exact transportedAffine_curve_eq W hΔ 1 1 a b f g h
  · apply transportedPolynomial_curve_eq W hΔ 1 1 a 2 f g
    exact h
  · apply transportedInfinity_curve_eq W hΔ a f g
    exact h
  · symm
    apply transportedPolynomial_curve_eq W hΔ 1 1 b 2 g f
    exact h.symm
  · have he : f = g := (cancel_mono (projectiveAdditionInclusion W 1 1 2)).mp
      h
    exact congrArg (fun t => t ≫ yProductCurveLocal W hΔ ⟨.polynomial, b⟩) he
  · symm
    apply infinityPolynomial_curve_eq W 2 g f
    exact h.symm
  · symm
    apply transportedInfinity_curve_eq W hΔ b g f
    exact h.symm
  · apply infinityPolynomial_curve_eq W 2 f g
    exact h
  · have he : f = g := (cancel_mono (infinityAdditionInclusion W)).mp
      h
    exact congrArg (fun t => t ≫ yProductCurveLocal W hΔ ⟨.infinity, b⟩) he

/-- A regular addition morphism on all pairs in the Y-chart in good reduction. -/
def yProductAdditionToCurve : Spec (.of (ChartProduct W 1 1)) ⟶ integralCurve W :=
  (yProductAdditionCover W hΔ).glueMorphisms (yProductCurveLocal W hΔ)
    (fun i j => yProductCurveLocal_commonScheme W hΔ i j _ _ pullback.condition)

/-- Each original local law is recovered by restricting the glued morphism. -/
theorem yProductCurveLocal_glued (i : (yProductAdditionCover W hΔ).I₀) :
    (yProductAdditionCover W hΔ).f i ≫ yProductAdditionToCurve W hΔ =
      yProductCurveLocal W hΔ i :=
  (yProductAdditionCover W hΔ).ι_glueMorphisms _ _ i

end FLT.Mazur.WeierstrassIntegralChart
