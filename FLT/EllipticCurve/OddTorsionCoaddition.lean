/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.OddTorsionOrderTensor
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
