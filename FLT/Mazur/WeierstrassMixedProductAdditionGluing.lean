/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLocalAdditionCurveComparison
public import FLT.Mazur.WeierstrassInputAdditionCovers

/-!
# Gluing addition on input products with an affine factor

The five-member cover has compatible curve-valued laws. They descend to a
regular morphism on each mixed Y/Z input-chart product in good reduction.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)
  (j k : Fin 3) (hj : j = 1 ∨ j = 2) (hk : k = 1 ∨ k = 2) (ha : j = 2 ∨ k = 2)

/-- The affine refinement has the existing transported-domain inclusion. -/
theorem mixedProductAdditionCover_affine_f (i : AdditionChartIndex) :
    (mixedProductAdditionCover W hΔ j k hj hk ha).f ⟨true, i⟩ =
      transportedPolynomialDomainMap W j k i hΔ := rfl

/-- The singleton polynomial refinement retains its original inclusion. -/
theorem mixedProductAdditionCover_polynomial_f (i : PUnit) :
    (mixedProductAdditionCover W hΔ j k hj hk ha).f ⟨false, i⟩ =
      projectiveAdditionInclusion W j k 2 := by
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

/-- Each local mixed-product law has the integral cubic as its common target. -/
def mixedProductCurveLocal (i : (mixedProductAdditionCover W hΔ j k hj hk ha).I₀) :
    (mixedProductAdditionCover W hΔ j k hj hk ha).X i ⟶ integralCurve W :=
  mixedProductAdditionSpec W hΔ j k hj hk ha i ≫
    integralCurveChart W (mixedProductAdditionOutput W hΔ j k hj hk ha i)

/-- The five local laws agree on any scheme with the same original input pair. -/
theorem mixedProductCurveLocal_commonScheme
    (i l : (mixedProductAdditionCover W hΔ j k hj hk ha).I₀) {X : Scheme.{u}}
    (f : X ⟶ (mixedProductAdditionCover W hΔ j k hj hk ha).X i)
    (g : X ⟶ (mixedProductAdditionCover W hΔ j k hj hk ha).X l)
    (h : f ≫ (mixedProductAdditionCover W hΔ j k hj hk ha).f i =
      g ≫ (mixedProductAdditionCover W hΔ j k hj hk ha).f l) :
    f ≫ mixedProductCurveLocal W hΔ j k hj hk ha i =
      g ≫ mixedProductCurveLocal W hΔ j k hj hk ha l := by
  rcases i with ⟨i, a⟩
  rcases l with ⟨l, b⟩
  cases i <;> cases l <;>
    simp only [mixedProductAdditionCover_affine_f, mixedProductAdditionCover_polynomial_f] at h
  · have he : f = g := (cancel_mono (projectiveAdditionInclusion W j k 2)).mp
      h
    exact congrArg (fun t => t ≫ mixedProductCurveLocal W hΔ j k hj hk ha ⟨false, b⟩) he
  · symm
    apply transportedPolynomial_curve_eq W hΔ j k b 2 g f
    exact h.symm
  · apply transportedPolynomial_curve_eq W hΔ j k a 2 f g
    exact h
  · exact transportedAffine_curve_eq W hΔ j k a b f g h

/-- Addition on the whole input-chart product with at least one affine factor. -/
def mixedProductAdditionToCurve : Spec (.of (ChartProduct W j k)) ⟶ integralCurve W :=
  (mixedProductAdditionCover W hΔ j k hj hk ha).glueMorphisms
    (mixedProductCurveLocal W hΔ j k hj hk ha)
    (fun i l => mixedProductCurveLocal_commonScheme W hΔ j k hj hk ha i l _ _
      pullback.condition)

/-- The glued morphism retains each of the five original local formulas. -/
theorem mixedProductCurveLocal_glued
    (i : (mixedProductAdditionCover W hΔ j k hj hk ha).I₀) :
    (mixedProductAdditionCover W hΔ j k hj hk ha).f i ≫
        mixedProductAdditionToCurve W hΔ j k hj hk ha =
      mixedProductCurveLocal W hΔ j k hj hk ha i :=
  (mixedProductAdditionCover W hΔ j k hj hk ha).ι_glueMorphisms _ _ i

end FLT.Mazur.WeierstrassIntegralChart
