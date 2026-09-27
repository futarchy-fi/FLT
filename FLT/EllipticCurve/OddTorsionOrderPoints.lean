/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.OddTorsionOrder

/-!
# Points of the integral odd-torsion coordinate order

Evaluation identifies the points of the coordinate order with the odd torsion
of the elliptic curve. This is a set-theoretic comparison; a group comparison
requires the integral comultiplication still missing from the order.
-/

@[expose] public section

open Polynomial
namespace WeierstrassCurve
universe u
variable {R k : Type u} [CommRing R] [Field k] [Algebra R k] [DecidableEq k]
    (W : WeierstrassCurve R) {n : ℕ} (hn : Odd n) (ξ η : R)
    (hT : (W.map (algebraMap R k)).toAffine.Nonsingular
      (algebraMap R k ξ) (algebraMap R k η))
    (htwo : 2 • Affine.Point.some _ _ hT = 0)

include hn htwo in
/-- Translated coordinates distinguish every odd-torsion point, including infinity. -/
theorem translatedTorsionCoordinates_injective :
    Function.Injective (W.translatedTorsionCoordinates (n := n) ξ η hT) := by
  intro P Q hPQ
  obtain ⟨x, y, h, he, _⟩ :=
    (W.map (algebraMap R k)).exists_affine_odd_torsion_translate hn hT htwo P.val
      (AddSubgroup.torsionBy.nsmul_iff.mp P.property)
  obtain ⟨x', y', h', he', _⟩ :=
    (W.map (algebraMap R k)).exists_affine_odd_torsion_translate hn hT htwo Q.val
      (AddSubgroup.torsionBy.nsmul_iff.mp Q.property)
  simp only [translatedTorsionCoordinates, he, he', Affine.Point.coordinates,
    Prod.mk.injEq] at hPQ
  apply Subtype.ext
  apply add_right_cancel (b := Affine.Point.some _ _ hT)
  rw [he, he']
  obtain ⟨rfl, rfl⟩ := hPQ
  rfl

/-- A torsion point evaluates every function in the integral coordinate order. -/
noncomputable def oddTorsionEvaluationPoint (P : W.oddTorsionPointSet (k := k) n) :
    W.oddTorsionCoordinateOrder hn ξ η hT htwo →ₐ[R] k :=
  (Pi.evalAlgHom R _ P).comp (W.oddTorsionCoordinateOrder hn ξ η hT htwo).val

/-- Distinct torsion points give distinct algebra maps from the coordinate order. -/
theorem oddTorsionEvaluationPoint_injective :
    Function.Injective (W.oddTorsionEvaluationPoint hn ξ η hT htwo) := by
  intro P Q hPQ
  apply W.translatedTorsionCoordinates_injective hn ξ η hT htwo
  let e := W.translatedTorsionEvaluation hn ξ η hT htwo
  apply Prod.ext
  · have he := DFunLike.congr_fun hPQ (e.rangeRestrict (W.torsionEnvelopeXCoord n ξ))
    change e (W.torsionEnvelopeXCoord n ξ) P = e (W.torsionEnvelopeXCoord n ξ) Q at he
    simpa only [e, translatedTorsionEvaluation_x] using he
  · have he := DFunLike.congr_fun hPQ (e.rangeRestrict (W.torsionEnvelopeYCoord n ξ))
    change e (W.torsionEnvelopeYCoord n ξ) P = e (W.torsionEnvelopeYCoord n ξ) Q at he
    simpa only [e, translatedTorsionEvaluation_y] using he

variable [(W.map (algebraMap R k)).IsElliptic]

/-- Every field-valued point of the integral coordinate order is evaluation
at an odd-torsion point of the elliptic curve. -/
theorem oddTorsionEvaluationPoint_surjective :
    Function.Surjective (W.oddTorsionEvaluationPoint hn ξ η hT htwo) := by
  intro f
  let e := W.translatedTorsionEvaluation hn ξ η hT htwo
  let g := f.comp e.rangeRestrict
  let x := g (W.torsionEnvelopeXCoord n ξ)
  let y := g (W.torsionEnvelopeYCoord n ξ)
  have hr : aeval x (W.multiplicationFiberPolynomial n ξ) = 0 ∧
      (W.map (algebraMap R k)).toAffine.Equation x y :=
    (W.torsionEnvelopePointsEquiv k n ξ g).property
  have h : (W.map (algebraMap R k)).toAffine.Nonsingular x y :=
    Affine.equation_iff_nonsingular.mp hr.2
  have hx : ((W.map (algebraMap R k)).multiplicationFiberPolynomial n
      (algebraMap R k ξ)).IsRoot x := by
    simpa only [map_multiplicationFiberPolynomial, Polynomial.IsRoot,
      eval_map_algebraMap] using hr.1
  have hm := ((W.map (algebraMap R k)).isRoot_multiplicationFiberPolynomial_iff_nsmul_eq_two_torsion
    h hT htwo n).mp hx
  let P : W.oddTorsionPointSet (k := k) n :=
    ⟨Affine.Point.some x y h - Affine.Point.some _ _ hT, by
      apply AddSubgroup.torsionBy.nsmul_iff.mpr
      rw [nsmul_sub, hm, odd_nsmul_of_two_nsmul_eq_zero hn htwo, sub_self]⟩
  have hP : W.translatedTorsionCoordinates ξ η hT P = (x, y) := by
    simp only [translatedTorsionCoordinates, P, sub_add_cancel, Affine.Point.coordinates]
  refine ⟨P, ?_⟩
  have he : (W.oddTorsionEvaluationPoint hn ξ η hT htwo P).comp e.rangeRestrict = g := by
    apply W.torsionEnvelope_hom_ext n ξ
    · change W.translatedTorsionEvaluation hn ξ η hT htwo (W.torsionEnvelopeXCoord n ξ) P = x
      rw [W.translatedTorsionEvaluation_x, hP]
    · change W.translatedTorsionEvaluation hn ξ η hT htwo (W.torsionEnvelopeYCoord n ξ) P = y
      rw [W.translatedTorsionEvaluation_y, hP]
  apply AlgHom.ext
  intro a
  obtain ⟨b, rfl⟩ := e.rangeRestrict_surjective a
  exact DFunLike.congr_fun he b

/-- The integral coordinate order has exactly the odd-torsion points over the
chosen field, with no extra points from its affine envelope. -/
noncomputable def oddTorsionCoordinatePointsEquiv :
    W.oddTorsionPointSet (k := k) n ≃
      (W.oddTorsionCoordinateOrder hn ξ η hT htwo →ₐ[R] k) :=
  Equiv.ofBijective (W.oddTorsionEvaluationPoint hn ξ η hT htwo)
    ⟨W.oddTorsionEvaluationPoint_injective hn ξ η hT htwo,
      W.oddTorsionEvaluationPoint_surjective hn ξ η hT htwo⟩

end WeierstrassCurve
