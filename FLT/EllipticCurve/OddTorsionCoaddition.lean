/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.OddTorsionOrderTensor
public import FLT.EllipticCurve.RCBComparison
public import FLT.EllipticCurve.RCBIntegral

/-!
# Constructing integral coaddition from its two coordinate functions

An injective evaluation map turns integral preimages of the translated sum
coordinates into an algebra map from the coordinate order. No Hopf structure
is assumed in this construction.
-/

@[expose] public section

open scoped TensorProduct
open Polynomial
universe u
namespace WeierstrassCurve
variable {R k : Type u} [CommRing R] [Field k] [Algebra R k] [DecidableEq k]
    (W : WeierstrassCurve R) {n : ℕ} (hn : Odd n) (ξ η : R)
    (hT : (W.map (algebraMap R k)).toAffine.Nonsingular
      (algebraMap R k ξ) (algebraMap R k η))
    (htwo : 2 • Affine.Point.some _ _ hT = 0)
/-- Integral preimages of both translated sum coordinates uniquely determine
a coaddition map into any algebra with injective evaluation on pairs. -/
theorem exists_oddTorsionCoaddition_of_coordinates (A : Type u) [CommRing A] [Algebra R A]
    (ev : A →ₐ[R] ((W.oddTorsionPointSet (k := k) n × W.oddTorsionPointSet (k := k) n) → k))
    (hi : Function.Injective (ev))
    (hx : (fun P : W.oddTorsionPointSet (k := k) n × W.oddTorsionPointSet (k := k) n =>
      (W.translatedTorsionCoordinates ξ η hT (P.1 + P.2)).1) ∈
        (ev).range)
    (hy : (fun P : W.oddTorsionPointSet (k := k) n × W.oddTorsionPointSet (k := k) n =>
      (W.translatedTorsionCoordinates ξ η hT (P.1 + P.2)).2) ∈
        (ev).range) :
    ∃ d : W.oddTorsionCoordinateOrder hn ξ η hT htwo →ₐ[R]
        A,
      ∀ f P Q, ev (d f) (P, Q) =
        f.val (P + Q) := by
  let e := W.translatedTorsionEvaluation hn ξ η hT htwo
  let H := e.range
  obtain ⟨x, hx⟩ := hx
  obtain ⟨y, hy⟩ := hy
  change ev x = _ at hx
  change ev y = _ at hy
  have hxr : aeval x (W.multiplicationFiberPolynomial n ξ) = 0 := by
    apply hi
    rw [map_zero, ← aeval_algHom_apply]
    ext P
    rw [aeval_pi_apply₂]
    change aeval (ev x P) _ = 0
    rw [congrFun hx P]
    exact (W.translatedTorsionCoordinates_relations hn ξ η hT htwo (P.1 + P.2)).1
  have hyr : (W.map (algebraMap R (A))).toAffine.Equation x y := by
    rw [Affine.equation_iff']
    change y ^ 2 + algebraMap R _ W.a₁ * x * y + algebraMap R _ W.a₃ * y -
      (x ^ 3 + algebraMap R _ W.a₂ * x ^ 2 + algebraMap R _ W.a₄ * x +
        algebraMap R _ W.a₆) = 0
    apply hi
    simp only [map_sub, map_add, map_mul, map_pow, AlgHom.commutes, map_zero, hx, hy]
    ext P
    exact ((W.map (algebraMap R k)).toAffine.equation_iff' _ _).mp
      (W.translatedTorsionCoordinates_relations hn ξ η hT htwo (P.1 + P.2)).2
  let F : W.torsionEnvelope n ξ →ₐ[R] A :=
    W.torsionEnvelopeLift (S := A) n ξ x y hxr hyr
  let sum : H →ₐ[R]
      ((W.oddTorsionPointSet (k := k) n × W.oddTorsionPointSet (k := k) n) → k) :=
    AlgHom.pi fun P => (Pi.evalAlgHom R _ (P.1 + P.2)).comp H.val
  have he : ev.comp F = sum.comp e.rangeRestrict := by
    refine W.torsionEnvelope_hom_ext n ξ (f := ev.comp F) (g := sum.comp e.rangeRestrict) ?_ ?_
    · ext P
      change ev (F (W.torsionEnvelopeXCoord n ξ)) P = e (W.torsionEnvelopeXCoord n ξ) (P.1 + P.2)
      rw [torsionEnvelopeLift_x, translatedTorsionEvaluation_x]
      exact congrFun hx P
    · ext P
      change ev (F (W.torsionEnvelopeYCoord n ξ)) P = e (W.torsionEnvelopeYCoord n ξ) (P.1 + P.2)
      rw [torsionEnvelopeLift_y, translatedTorsionEvaluation_y]
      exact congrFun hy P
  have hker : RingHom.ker e.rangeRestrict.toRingHom ≤ RingHom.ker F.toRingHom := by
    intro a ha
    change F a = 0
    apply hi
    rw [map_zero]
    have hz : e a = 0 := congrArg Subtype.val (show e.rangeRestrict a = 0 from ha)
    ext P
    have hh := congrFun (DFunLike.congr_fun he a) P
    change ev (F a) P = e a (P.1 + P.2) at hh
    rw [hh, hz]
    rfl
  let d := AlgHom.liftOfSurjective e.rangeRestrict e.rangeRestrict_surjective F hker
  refine ⟨d, ?_⟩
  intro f P Q
  obtain ⟨a, rfl⟩ := e.rangeRestrict_surjective f
  change ev (d (e.rangeRestrict a)) (P, Q) = e a (P + Q)
  rw [AlgHom.liftOfSurjective_apply]
  exact congrFun (DFunLike.congr_fun he a) (P, Q)
end WeierstrassCurve

namespace WeierstrassCurve
variable {R k : Type u} [CommRing R] [Field k] [Algebra R k] [DecidableEq k]
    (W : WeierstrassCurve R) [W.IsShortNF] {n : ℕ} (hn : Odd n) (ξ : R)
    (hT : (W.map (algebraMap R k)).toAffine.Nonsingular
      (algebraMap R k ξ) (algebraMap R k 0))
    (htwo : 2 • Affine.Point.some _ _ hT = 0)
set_option maxHeartbeats 800000 in
-- Unfolding the tensor order and its two universal points requires a larger elaboration budget.
set_option backward.isDefEq.respectTransparency false in
/-- Explicit integral coordinates of the translated group sum, constructed
using the unit RCB Y-coordinate and polynomial translation on its chart. -/
theorem exists_integral_oddTorsionAdditionCoordinates (hΔ : IsUnit W.Δ) (h2 : IsUnit (2 : R))
    (ht : W.toAffine.Equation ξ 0) :
    ∃ c : (W.oddTorsionCoordinateOrder hn ξ 0 hT htwo ⊗[R]
      W.oddTorsionCoordinateOrder hn ξ 0 hT htwo) ×
      (W.oddTorsionCoordinateOrder hn ξ 0 hT htwo ⊗[R]
        W.oddTorsionCoordinateOrder hn ξ 0 hT htwo),
      ∀ P Q : W.oddTorsionPointSet (k := k) n,
        (W.oddTorsionTensorEvaluation hn ξ 0 hT htwo c.1 (P, Q),
          W.oddTorsionTensorEvaluation hn ξ 0 hT htwo c.2 (P, Q)) =
            W.translatedTorsionCoordinates ξ 0 hT (P + Q) := by
  let e := W.translatedTorsionEvaluation hn ξ 0 hT htwo
  let H := e.range
  let A := H ⊗[R] H
  let ev : A →ₐ[R] ((W.oddTorsionPointSet (k := k) n × W.oddTorsionPointSet (k := k) n) → k) :=
    W.oddTorsionTensorEvaluation hn ξ 0 hT htwo
  let e1 : W.torsionEnvelope n ξ →ₐ[R] A := Algebra.TensorProduct.includeLeft.comp e.rangeRestrict
  let e2 : W.torsionEnvelope n ξ →ₐ[R] A := Algebra.TensorProduct.includeRight.comp e.rangeRestrict
  let x1 := e1 (W.torsionEnvelopeXCoord n ξ)
  let y1 := e1 (W.torsionEnvelopeYCoord n ξ)
  let x2 := e2 (W.torsionEnvelopeXCoord n ξ)
  let y2 := e2 (W.torsionEnvelopeYCoord n ξ)
  let E : WeierstrassCurve A := W.map (algebraMap R A)
  let : E.IsShortNF := ⟨by simp [E, map], by simp [E, map, a₂_of_isShortNF], by simp [E, map]⟩
  have hr1 := (W.torsionEnvelopePointsEquiv A n ξ e1).property
  have hr2 := (W.torsionEnvelopePointsEquiv A n ξ e2).property
  change aeval x1 (W.multiplicationFiberPolynomial n ξ) = 0 ∧ E.toAffine.Equation x1 y1 at hr1
  change aeval x2 (W.multiplicationFiberPolynomial n ξ) = 0 ∧ E.toAffine.Equation x2 y2 at hr2
  let X := RCB.addX E.a₄ E.a₆ x1 y1 1 x2 y2 1
  let Y := RCB.addY E.a₄ E.a₆ x1 y1 1 x2 y2 1
  let Z := RCB.addZ E.a₄ E.a₆ x1 y1 1 x2 y2 1
  have hY : IsUnit Y := by
    apply RCB.isUnit_addY_of_multiplicationFiber E
      (by simpa only [E, map_Δ] using hΔ.map (algebraMap R A))
      (by simpa only [map_ofNat] using h2.map (algebraMap R A)) hn (algebraMap R A ξ)
      x1 y1 x2 y2 (by simpa only [map_zero] using ht.map (S := A) (algebraMap R A)) hr1.2 hr2.2
    · simpa only [E, map_multiplicationFiberPolynomial, eval_map_algebraMap] using hr1.1
    · simpa only [E, map_multiplicationFiberPolynomial, eval_map_algebraMap] using hr2.1
  let U := hY.unit
  let u := X * (↑U⁻¹ : A)
  let v := Z * (↑U⁻¹ : A)
  let cx := TwoTorsionChart.translateX E.a₄ (algebraMap R A ξ) u v
  let cy := TwoTorsionChart.translateY E.a₄ (algebraMap R A ξ) u v
  refine ⟨(cx, cy), ?_⟩
  intro P Q
  let φ : A →ₐ[R] k := (Pi.evalAlgHom R _ (P, Q)).comp ev
  have hev1 (a : W.torsionEnvelope n ξ) : φ (e1 a) = e a P := by
    change W.oddTorsionTensorEvaluation hn ξ 0 hT htwo
      ((e.rangeRestrict a) ⊗ₜ[R] 1) (P, Q) = e a P
    rw [oddTorsionTensorEvaluation_tmul]
    change e a P * 1 = e a P
    rw [mul_one]
  have hev2 (a : W.torsionEnvelope n ξ) : φ (e2 a) = e a Q := by
    change W.oddTorsionTensorEvaluation hn ξ 0 hT htwo
      (1 ⊗ₜ[R] (e.rangeRestrict a)) (P, Q) = e a Q
    rw [oddTorsionTensorEvaluation_tmul]
    change 1 * e a Q = e a Q
    rw [one_mul]
  let E' := W.map (algebraMap R k)
  let : E'.IsShortNF := ⟨by simp [E', map], by simp [E', map, a₂_of_isShortNF], by simp [E', map]⟩
  let : NeZero (2 : k) := ⟨by simpa only [map_ofNat] using (h2.map (algebraMap R k)).ne_zero⟩
  have ht' : E'.toAffine.Nonsingular (algebraMap R k ξ) 0 := by simpa only [map_zero] using hT
  let T := Affine.Point.some _ _ ht'
  have ht2 : 2 • T = 0 := by simpa only [map_zero] using htwo
  have hp0 : n • P.val = 0 := AddSubgroup.torsionBy.nsmul_iff.mp P.property
  have hq0 : n • Q.val = 0 := AddSubgroup.torsionBy.nsmul_iff.mp Q.property
  obtain ⟨xp, yp, hp, hpEq, _⟩ := E'.exists_affine_odd_torsion_translate hn ht' ht2 P.val hp0
  obtain ⟨xq, yq, hq, hqEq, _⟩ := E'.exists_affine_odd_torsion_translate hn ht' ht2 Q.val hq0
  have hpC : W.translatedTorsionCoordinates ξ 0 hT P = (xp, yp) := by
    simp only [translatedTorsionCoordinates, map_zero, hpEq, Affine.Point.coordinates]
  have hqC : W.translatedTorsionCoordinates ξ 0 hT Q = (xq, yq) := by
    simp only [translatedTorsionCoordinates, map_zero, hqEq, Affine.Point.coordinates]
  have hx1 : φ x1 = xp := by
    rw [hev1]
    rw [translatedTorsionEvaluation_x, hpC]
  have hy1 : φ y1 = yp := by
    rw [hev1]
    rw [translatedTorsionEvaluation_y, hpC]
  have hx2 : φ x2 = xq := by
    rw [hev2]
    rw [translatedTorsionEvaluation_x, hqC]
  have hy2 : φ y2 = yq := by
    rw [hev2]
    rw [translatedTorsionEvaluation_y, hqC]
  have hXφ : φ X = RCB.addX E'.a₄ E'.a₆ xp yp 1 xq yq 1 := by
    simp only [X, RCB.addX, map_sub, map_add, map_mul, map_pow, map_ofNat, map_one,
      E, WeierstrassCurve.map, AlgHom.commutes, hx1, hy1, hx2, hy2, E']
  have hYφ : φ Y = RCB.addY E'.a₄ E'.a₆ xp yp 1 xq yq 1 := by
    simp only [Y, RCB.addY, map_sub, map_add, map_mul, map_pow, map_ofNat, map_one,
      E, WeierstrassCurve.map, AlgHom.commutes, hx1, hy1, hx2, hy2, E']
  have hZφ : φ Z = RCB.addZ E'.a₄ E'.a₆ xp yp 1 xq yq 1 := by
    simp only [Z, RCB.addZ, map_add, map_mul, map_ofNat, map_one,
      E, WeierstrassCurve.map, AlgHom.commutes, hx1, hy1, hx2, hy2, E']
  have hsum : n • (Affine.Point.some xp yp hp + Affine.Point.some xq yq hq) = 0 := by
    rw [← hpEq, ← hqEq, nsmul_add, nsmul_add, nsmul_add, hp0, hq0,
      odd_nsmul_of_two_nsmul_eq_zero hn ht2, zero_add]
    simpa only [two_nsmul] using ht2
  have hdiff : n • (Affine.Point.some xp yp hp - Affine.Point.some xq yq hq) = 0 := by
    rw [← hpEq, ← hqEq, nsmul_sub, nsmul_add, nsmul_add, hp0, hq0, sub_self]
  have hc := RCB.translated_normalized_add E' ht' hp hq hn hsum hdiff
  have hu : φ u = RCB.addX E'.a₄ E'.a₆ xp yp 1 xq yq 1 /
      RCB.addY E'.a₄ E'.a₆ xp yp 1 xq yq 1 := by
    rw [map_mul, map_units_inv, show (↑U : A) = Y from hY.unit_spec, hXφ, hYφ, div_eq_mul_inv]
  have hv : φ v = RCB.addZ E'.a₄ E'.a₆ xp yp 1 xq yq 1 /
      RCB.addY E'.a₄ E'.a₆ xp yp 1 xq yq 1 := by
    rw [map_mul, map_units_inv, show (↑U : A) = Y from hY.unit_spec, hZφ, hYφ, div_eq_mul_inv]
  have hgroup : Affine.Point.some xp yp hp + Affine.Point.some xq yq hq + T =
      (P + Q).val + T := by
    rw [← hpEq, ← hqEq]
    change (P.val + T) + (Q.val + T) + T = (P.val + Q.val) + T
    calc
      _ = ((P.val + Q.val) + T) + (T + T) := by abel
      _ = _ := by rw [← two_nsmul, ht2, add_zero]
  change (φ cx, φ cy) = _
  have hm : (φ cx, φ cy) =
      (TwoTorsionChart.translateX E'.a₄ (algebraMap R k ξ) (φ u) (φ v),
        TwoTorsionChart.translateY E'.a₄ (algebraMap R k ξ) (φ u) (φ v)) := by
    simp only [cx, cy, TwoTorsionChart.translateX, TwoTorsionChart.translateY,
      TwoTorsionChart.factor, map_neg, map_sub, map_add, map_mul, map_pow, map_ofNat,
      map_one, E, E', WeierstrassCurve.map, AlgHom.commutes]
  rw [hm, hu, hv]
  exact hc.trans (by
    rw [hgroup]
    simp only [translatedTorsionCoordinates, map_zero]
    rfl)
/-- Integral coaddition for a short good-reduction model with an integral
nonzero two-torsion point, over a Dedekind domain with perfect fraction field. -/
theorem exists_oddTorsionCoaddition_short
    [IsDedekindDomain R] [Module.IsTorsionFree R k]
    (K : Type u) [Field K] [PerfectField K] [Algebra R K] [IsFractionRing R K]
    [Algebra K k] [IsScalarTower R K k] [IsGalois K k] [IsSepClosed k]
    (hΔ : IsUnit W.Δ) (h2 : IsUnit (2 : R)) (ht : W.toAffine.Equation ξ 0) :
    ∃ d : W.oddTorsionCoordinateOrder hn ξ 0 hT htwo →ₐ[R]
        (W.oddTorsionCoordinateOrder hn ξ 0 hT htwo ⊗[R]
          W.oddTorsionCoordinateOrder hn ξ 0 hT htwo),
      ∀ f P Q, W.oddTorsionTensorEvaluation hn ξ 0 hT htwo (d f) (P, Q) =
        f.val (P + Q) := by
  let : W.IsElliptic := ⟨hΔ⟩
  obtain ⟨c, hc⟩ := W.exists_integral_oddTorsionAdditionCoordinates hn ξ hT htwo hΔ h2 ht
  apply W.exists_oddTorsionCoaddition_of_coordinates hn ξ 0 hT htwo _
    (W.oddTorsionTensorEvaluation hn ξ 0 hT htwo)
    (W.oddTorsionTensorEvaluation_injective hn ξ 0 hT htwo K)
  · exact ⟨c.1, funext fun P => congrArg Prod.fst (hc P.1 P.2)⟩
  · exact ⟨c.2, funext fun P => congrArg Prod.snd (hc P.1 P.2)⟩

end WeierstrassCurve
