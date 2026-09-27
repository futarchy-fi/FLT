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
of the elliptic curve. The additive and equivariant comparison using integral
coaddition is proved in `OddTorsionFlat`.
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

set_option backward.isDefEq.respectTransparency false in
/-- A field algebra map acts on the odd-torsion subgroup by mapping coordinates. -/
noncomputable def oddTorsionPointMap (σ : k →ₐ[R] k) :
    W.oddTorsionPointSet (k := k) n →+ W.oddTorsionPointSet (k := k) n where
  toFun P := ⟨Affine.Point.map (W' := W.toAffine) σ P.val, by
    apply AddSubgroup.torsionBy.nsmul_iff.mpr
    exact ((Affine.Point.map (W' := W.toAffine) σ).map_nsmul n P.val).symm.trans
      ((congrArg (Affine.Point.map (W' := W.toAffine) σ)
        (AddSubgroup.torsionBy.nsmul_iff.mp P.property)).trans (map_zero _))⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' P Q := Subtype.ext (map_add _ P.val Q.val)

include hn htwo in
set_option backward.isDefEq.respectTransparency false in
/-- Translated torsion coordinates commute with field algebra maps fixing the
integral coefficients and the translating two-torsion point. -/
theorem translatedTorsionCoordinates_map (σ : k →ₐ[R] k)
    (P : W.oddTorsionPointSet (k := k) n) :
    W.translatedTorsionCoordinates ξ η hT (W.oddTorsionPointMap σ P) =
      (σ (W.translatedTorsionCoordinates ξ η hT P).1,
        σ (W.translatedTorsionCoordinates ξ η hT P).2) := by
  obtain ⟨x, y, h, he, _⟩ :=
    (W.map (algebraMap R k)).exists_affine_odd_torsion_translate hn hT htwo P.val
      (AddSubgroup.torsionBy.nsmul_iff.mp P.property)
  have ht : Affine.Point.map (W' := W.toAffine) σ (Affine.Point.some _ _ hT) =
      Affine.Point.some _ _ hT := by
    simp only [Affine.Point.map_some, AlgHom.commutes]
  have hp : (W.oddTorsionPointMap σ P).val + Affine.Point.some _ _ hT =
      Affine.Point.map (W' := W.toAffine) σ (P.val + Affine.Point.some _ _ hT) := by
    rw [map_add, ht]
    rfl
  simp only [translatedTorsionCoordinates, hp, he, Affine.Point.map_some,
    Affine.Point.coordinates]

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation at torsion points is equivariant for every automorphism of the
geometric field fixing the coefficient ring. -/
theorem oddTorsionEvaluationPoint_equivariant (σ : k ≃ₐ[R] k)
    (P : W.oddTorsionPointSet (k := k) n) :
    W.oddTorsionEvaluationPoint hn ξ η hT htwo (W.oddTorsionPointMap σ.toAlgHom P) =
      σ.toAlgHom.comp (W.oddTorsionEvaluationPoint hn ξ η hT htwo P) := by
  let e := W.translatedTorsionEvaluation hn ξ η hT htwo
  have he : (W.oddTorsionEvaluationPoint hn ξ η hT htwo
      (W.oddTorsionPointMap σ.toAlgHom P)).comp e.rangeRestrict =
      (σ.toAlgHom.comp (W.oddTorsionEvaluationPoint hn ξ η hT htwo P)).comp
        e.rangeRestrict := by
    apply W.torsionEnvelope_hom_ext n ξ
    · change e (W.torsionEnvelopeXCoord n ξ) (W.oddTorsionPointMap σ.toAlgHom P) =
        σ (e (W.torsionEnvelopeXCoord n ξ) P)
      simpa only [e, translatedTorsionEvaluation_x, AlgEquiv.coe_toAlgHom] using
        congrArg Prod.fst (W.translatedTorsionCoordinates_map hn ξ η hT htwo σ.toAlgHom P)
    · change e (W.torsionEnvelopeYCoord n ξ) (W.oddTorsionPointMap σ.toAlgHom P) =
        σ (e (W.torsionEnvelopeYCoord n ξ) P)
      simpa only [e, translatedTorsionEvaluation_y, AlgEquiv.coe_toAlgHom] using
        congrArg Prod.snd (W.translatedTorsionCoordinates_map hn ξ η hT htwo σ.toAlgHom P)
  apply AlgHom.ext
  intro a
  obtain ⟨b, rfl⟩ := e.rangeRestrict_surjective a
  exact DFunLike.congr_fun he b

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
