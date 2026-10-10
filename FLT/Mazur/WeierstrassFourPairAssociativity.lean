/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassFiveAffineTriple
public import FLT.Mazur.WeierstrassInfinityTripleScalarMaps

/-!
# Associativity for compatible pairs with five affine presentations

The triple morphism is constructed from the pair data. This permits later
specialization of all four infinity laws to a new coefficient algebra, without
requiring a morphism from its spectrum back to the original triple member.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- Compatible genuine pair laws associate when the five input points have affine charts. -/
theorem integralCurveFourPairs_assoc {X : Scheme.{u}}
    (p : Fin 7 → (X ⟶ integralCurve W))
    (a : Fin 4 → (X ⟶ integralCurveProduct W))
    (hl : ∀ j, a j ≫ pullback.fst _ _ = p (infinityTripleLeftIndex j))
    (hr : ∀ j, a j ≫ pullback.snd _ _ = p (infinityTripleRightIndex j))
    (ho : ∀ j, a j ≫ integralCurveAddition W hΔ = p (infinityTripleOutputIndex j))
    (ha : ∀ i : Fin 5, ∃ q : X ⟶ chartScheme W 2,
      q ≫ integralCurveChart W 2 = p (i.castAdd 2)) : p 5 = p 6 := by
  have hb (j : Fin 4) :
      p (infinityTripleLeftIndex j) ≫ integralCurveStructure W =
        p (infinityTripleRightIndex j) ≫ integralCurveStructure W := by
    rw [← hl j, ← hr j, Category.assoc, Category.assoc, pullback.condition]
  have ht : a 0 ≫ integralCurveProductStructure W =
      p 2 ≫ integralCurveStructure W := by
    rw [integralCurveProductStructure, ← Category.assoc, hl]
    exact (hb 0).trans (hb 1)
  let t : X ⟶ integralCurveTriple W := pullback.lift (a 0) (p 2) ht
  have ht0 : t ≫ integralCurveTriplePair W = a 0 := pullback.lift_fst _ _ _
  have ht2 : t ≫ integralCurveTripleThird W = p 2 := pullback.lift_snd _ _ _
  have htp : t ≫ integralCurveTripleFirst W = p 0 := by
    rw [integralCurveTripleFirst, ← Category.assoc, ht0, hl]
    rfl
  have htq : t ≫ integralCurveTripleSecond W = p 1 := by
    rw [integralCurveTripleSecond, ← Category.assoc, ht0, hr]
    rfl
  have ht1 : t ≫ integralCurveTripleLastPair W = a 1 := by
    apply pullback.hom_ext
    · simpa only [Category.assoc, integralCurveTripleLastPair_fst, hl,
        show infinityTripleLeftIndex 1 = 1 from rfl] using htq
    · simpa only [Category.assoc, integralCurveTripleLastPair_snd, hr,
        show infinityTripleRightIndex 1 = 2 from rfl] using ht2
  have ht3 : t ≫ integralCurveAddFirstPair W hΔ = a 2 := by
    apply pullback.hom_ext
    · simp only [Category.assoc, integralCurveAddFirstPair_fst, hl]
      rw [← Category.assoc, ht0, ho]
      rfl
    · simpa only [Category.assoc, integralCurveAddFirstPair_snd, hr,
        show infinityTripleRightIndex 2 = 2 from rfl] using ht2
  have ht4 : t ≫ integralCurveAddLastPair W hΔ = a 3 := by
    apply pullback.hom_ext
    · simpa only [Category.assoc, integralCurveAddLastPair_fst, hl,
        show infinityTripleLeftIndex 3 = 0 from rfl] using htp
    · simp only [Category.assoc, integralCurveAddLastPair_snd, hr]
      rw [← Category.assoc, ht1, ho]
      rfl
  obtain ⟨p₀, hp₀⟩ := ha 0
  obtain ⟨p₁, hp₁⟩ := ha 1
  obtain ⟨p₂, hp₂⟩ := ha 2
  obtain ⟨p₃, hp₃⟩ := ha 3
  obtain ⟨p₄, hp₄⟩ := ha 4
  have he := integralCurveTripleAdd_of_fiveAffine W hΔ t p₀ p₁ p₂ p₃ p₄
    (hp₀.trans htp.symm) (hp₁.trans htq.symm) (hp₂.trans ht2.symm)
    (by rw [← Category.assoc, ht0, ho]; exact hp₃)
    (by rw [← Category.assoc, ht1, ho]; exact hp₄)
  simpa only [integralCurveTripleAddLeft, integralCurveTripleAddRight,
    ← Category.assoc, ht3, ht4, ho,
    show infinityTripleOutputIndex 2 = 5 from rfl,
    show infinityTripleOutputIndex 3 = 6 from rfl] using he

end FLT.Mazur.WeierstrassIntegralChart
