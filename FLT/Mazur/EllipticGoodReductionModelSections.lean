/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGeneralizedSmoothComparison
public import FLT.Mazur.EllipticE0GeometricGroup

/-!
# Original points in the genuine good-reduction generalized model

The existing E₀ equivalence maps into the constructed generalized elliptic
curve's actual group. Its underlying section and generic point remain the
original ones, and its addition is the previously constructed geometric law.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CartesianMonoidalCategory
open scoped MonObj

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (hΔ : IsUnit W.Δ)

/-- The actual group sections of the generalized elliptic model. -/
def goodReductionModelSections : CommGrpCat :=
  CommGrpCat.of (Over.mk (𝟙 (Spec (.of A))) ⟶
    (integralGeneralizedEllipticCurve W hΔ).group)

/-- The original E₀ point as a section of the genuine generalized elliptic model. -/
def e0ToGoodReductionModel (P : ellipticE0 A W) : goodReductionModelSections A W hΔ :=
  e0ToSmoothSection A W P ≫ integralSmoothOverInclusion W

/-- The generalized-model section is exactly the original integral section. -/
theorem e0ToGoodReductionModel_left (P : ellipticE0 A W) :
    (e0ToGoodReductionModel A W hΔ P).left = integralPointSection A W P.val :=
  smoothIntegralPointSection_inclusion A W P.val P.property

/-- Restriction to the generic fiber retains the original point, not a chosen replacement. -/
theorem e0ToGoodReductionModel_generic (P : ellipticE0 A W) :
    Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫
        (e0ToGoodReductionModel A W hΔ P).left = (projectiveToIntegral W P.val).left := by
  rw [e0ToGoodReductionModel_left, integralPointSection_generic]

/-- The original E₀ addition agrees with the generalized model's actual group law. -/
theorem e0ToGoodReductionModel_add (P Q : ellipticE0 A W) :
    e0ToGoodReductionModel A W hΔ (P + Q) =
      e0ToGoodReductionModel A W hΔ P * e0ToGoodReductionModel A W hΔ Q := by
  change e0ToSmoothSection A W (P + Q) ≫ integralSmoothOverInclusion W =
    lift (e0ToSmoothSection A W P ≫ integralSmoothOverInclusion W)
      (e0ToSmoothSection A W Q ≫ integralSmoothOverInclusion W) ≫
        integralCurveOverAddition W hΔ
  rw [e0ToSmoothSection_add, Category.assoc, integralSmoothOverInclusion_addition W hΔ,
    ← Category.assoc, lift_map]

/-- Every actual generalized-model group section is obtained from one original E₀ point. -/
theorem e0ToGoodReductionModel_bijective :
    Function.Bijective (e0ToGoodReductionModel A W hΔ) := by
  let _ := integralSmoothOverInclusion_isIso W hΔ
  constructor
  · intro P Q h
    apply e0ToSmoothSection_injective A W
    exact (cancel_mono (integralSmoothOverInclusion W)).mp h
  · intro s
    obtain ⟨P, hP⟩ := e0ToSmoothSection_surjective A W
      (s ≫ inv (integralSmoothOverInclusion W))
    refine ⟨P, ?_⟩
    change e0ToSmoothSection A W P ≫ integralSmoothOverInclusion W = s
    rw [hP, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- The arithmetic group is identified with the genuine generalized model's group sections. -/
def e0GoodReductionModelAddEquiv :
    ellipticE0 A W ≃+ Additive (goodReductionModelSections A W hΔ) where
  toEquiv := Equiv.ofBijective (fun P => Additive.ofMul (e0ToGoodReductionModel A W hΔ P))
    (e0ToGoodReductionModel_bijective A W hΔ)
  map_add' := e0ToGoodReductionModel_add A W hΔ

/-- The additive comparison keeps the original cubic section on every point. -/
theorem e0GoodReductionModelAddEquiv_left (P : ellipticE0 A W) :
    ((e0GoodReductionModelAddEquiv A W hΔ P).toMul).left = integralPointSection A W P.val :=
  e0ToGoodReductionModel_left A W hΔ P

end FLT.Mazur.WeierstrassIntegralChart
