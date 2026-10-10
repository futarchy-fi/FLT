/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRegularInputDescent
public import FLT.Mazur.WeierstrassSmoothTripleInputRegular
public import FLT.Mazur.WeierstrassFiniteChartDescent

/-!
# Affine inputs detect morphisms out of the full smooth pair

Flatness of the two smooth projections makes their normalized Z coordinates
regular. Injective localization then descends equality from affine inputs,
including over nonreduced coefficient rings and at bad reduction.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Two affine presentations suffice to detect maps from the entire smooth pair to the cubic. -/
theorem smoothPair_hom_ext_of_affine (f g : smoothFactorProduct W ⟶ integralCurve W)
    (h : ∀ (X : Scheme.{u}) (t : X ⟶ smoothFactorProduct W)
      (p q : X ⟶ chartScheme W 2),
      p ≫ integralCurveChart W 2 = t ≫ pullback.fst _ _ ≫ (integralSmoothOpen W).ι →
      q ≫ integralCurveChart W 2 = t ≫ pullback.snd _ _ ≫ (integralSmoothOpen W).ι →
      t ≫ f = t ≫ g) : f = g := by
  let points : Fin 4 → (smoothFactorProduct W ⟶ integralCurve W) :=
    ![pullback.fst _ _ ≫ (integralSmoothOpen W).ι,
      pullback.snd _ _ ≫ (integralSmoothOpen W).ι, f, g]
  apply finiteCurveCharts_hom_ext W 4 points
  intro X t ht b p hp
  let _ := ht
  apply Scheme.Cover.hom_ext X.affineCover
  intro i
  let a := X.affineCover.f i
  have he (k : Fin 4) : (a ≫ p k) ≫ integralCurveChart W (productChartCoordinate (b k)) =
      (a ≫ t) ≫ points k := by rw [Category.assoc, hp, Category.assoc]
  have hz (k : Fin 2) : IsRegular (specSectionHom (a ≫ p (k.castAdd 2))
      (coord W (productChartCoordinate (b (k.castAdd 2))) 2)) := by
    fin_cases k
    · exact smoothChart_z_regular_of_flat W ((a ≫ t) ≫ pullback.fst _ _)
        (b 0) (a ≫ p 0) (by simpa [points, Category.assoc] using he 0)
    · exact smoothChart_z_regular_of_flat W ((a ≫ t) ≫ pullback.snd _ _)
        (b 1) (a ≫ p 1) (by simpa [points, Category.assoc] using he 1)
  have hh : (a ≫ p 2) ≫ integralCurveChart W (productChartCoordinate (b 2)) =
      (a ≫ p 3) ≫ integralCurveChart W (productChartCoordinate (b 3)) := by
    apply chart_outputs_eq_of_regular_inputs W 2
      (fun k => productChartCoordinate (b (k.castAdd 2)))
      (fun k => a ≫ p (k.castAdd 2)) hz
    intro T _ v q hq
    have hl : q 0 ≫ integralCurveChart W 2 =
        (v ≫ a ≫ t) ≫ pullback.fst _ _ ≫ (integralSmoothOpen W).ι := by
      have h0 := hq 0
      change _ = v ≫ (a ≫ p 0) ≫ integralCurveChart W _ at h0
      rw [he 0] at h0
      simpa [points, Category.assoc] using h0
    have hr : q 1 ≫ integralCurveChart W 2 =
        (v ≫ a ≫ t) ≫ pullback.snd _ _ ≫ (integralSmoothOpen W).ι := by
      have h1 := hq 1
      change _ = v ≫ (a ≫ p 1) ≫ integralCurveChart W _ at h1
      rw [he 1] at h1
      simpa [points, Category.assoc] using h1
    have hv := h _ (v ≫ a ≫ t) (q 0) (q 1) hl hr
    rw [he 2, he 3]
    simpa [points, Category.assoc] using hv
  rw [he 2, he 3] at hh
  simpa [a, points, Category.assoc] using hh

end FLT.Mazur.WeierstrassIntegralChart
