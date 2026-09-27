/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.MultiplicationFiber
public import FLT.EllipticCurve.OddTorsionChart

/-!
# An affine envelope for odd torsion

Translation by a nonzero two-torsion point identifies odd torsion with an
entirely affine multiplication fibre. Adjoining the x-coordinate by the monic
multiplication-fibre equation and then the y-coordinate by the Weierstrass
equation gives a finite free envelope. The envelope itself is not the kernel
Hopf algebra: its generic fibre has multiplicities at the two-torsion target.
-/

@[expose] public section

open Polynomial
namespace WeierstrassCurve

section Translation
variable {G : Type*} [AddCommGroup G] {n : ℕ} {T : G}

/-- Multiplication by an odd integer fixes every point killed by two. -/
lemma odd_nsmul_of_two_nsmul_eq_zero (hn : Odd n) (hT : 2 • T = 0) : n • T = T := by
  obtain ⟨m, rfl⟩ := hn
  rw [add_nsmul, mul_nsmul, hT, smul_zero, one_nsmul, zero_add]

/-- Translation by a two-torsion point identifies odd torsion with its
multiplication fibre, including the identity of the torsion subgroup. -/
def oddTorsionTranslateEquiv (hn : Odd n) (hT : 2 • T = 0) :
    {P : G // n • P = 0} ≃ {Q : G // n • Q = T} where
  toFun P := ⟨P.val + T, by rw [nsmul_add, P.property,
    odd_nsmul_of_two_nsmul_eq_zero hn hT, zero_add]⟩
  invFun Q := ⟨Q.val - T, by rw [nsmul_sub, Q.property,
    odd_nsmul_of_two_nsmul_eq_zero hn hT, sub_self]⟩
  left_inv P := Subtype.ext (add_sub_cancel_right P.val T)
  right_inv Q := Subtype.ext (sub_add_cancel Q.val T)

/-- A multiplication fibre over a nonzero point avoids infinity. -/
lemma ne_zero_of_nsmul_eq_nonzero {Q : G} (hT : T ≠ 0) (hQ : n • Q = T) : Q ≠ 0 := by
  rintro rfl
  exact hT (by simpa only [smul_zero] using hQ.symm)

end Translation

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The x-coordinate algebra of the affine envelope over the target abscissa `ξ`. -/
abbrev torsionEnvelopeX (n : ℤ) (ξ : R) :=
  AdjoinRoot (W.multiplicationFiberPolynomial n ξ)

/-- The Weierstrass equation in y after adjoining an x-coordinate of the fibre. -/
noncomputable def torsionEnvelopeYPolynomial (n : ℤ) (ξ : R) :
    (W.torsionEnvelopeX n ξ)[X] :=
  W.toAffine.polynomial.map
    ((aeval (AdjoinRoot.root (W.multiplicationFiberPolynomial n ξ))).toRingHom)

/-- The affine envelope obtained by adjoining both coordinates of the fibre. -/
abbrev torsionEnvelope (n : ℤ) (ξ : R) := AdjoinRoot (W.torsionEnvelopeYPolynomial n ξ)

/-- The y-equation of the envelope is monic over the x-coordinate algebra. -/
lemma monic_torsionEnvelopeYPolynomial (n : ℤ) (ξ : R) :
    (W.torsionEnvelopeYPolynomial n ξ).Monic :=
  W.toAffine.monic_polynomial.map _

/-- The affine envelope is finite over the coefficient ring. -/
theorem finite_torsionEnvelope {n : ℤ} (hn : n ≠ 0) (ξ : R) :
    Module.Finite R (W.torsionEnvelope n ξ) := by
  let : Module.Finite R (W.torsionEnvelopeX n ξ) := W.finite_multiplicationFiber hn ξ
  let : Module.Finite (W.torsionEnvelopeX n ξ) (W.torsionEnvelope n ξ) :=
    (W.monic_torsionEnvelopeYPolynomial n ξ).finite_adjoinRoot
  exact Module.Finite.trans (W.torsionEnvelopeX n ξ) (W.torsionEnvelope n ξ)

/-- The affine envelope is free over the coefficient ring. -/
theorem free_torsionEnvelope {n : ℤ} (hn : n ≠ 0) (ξ : R) :
    Module.Free R (W.torsionEnvelope n ξ) := by
  let : Module.Free R (W.torsionEnvelopeX n ξ) :=
    (W.monic_multiplicationFiberPolynomial hn ξ).free_adjoinRoot
  let : Module.Free (W.torsionEnvelopeX n ξ) (W.torsionEnvelope n ξ) :=
    (W.monic_torsionEnvelopeYPolynomial n ξ).free_adjoinRoot
  exact Module.Free.trans (R := R) (S := W.torsionEnvelopeX n ξ)
    (M := W.torsionEnvelope n ξ)

/-- The affine envelope is flat over the coefficient ring. -/
theorem flat_torsionEnvelope {n : ℤ} (hn : n ≠ 0) (ξ : R) :
    Module.Flat R (W.torsionEnvelope n ξ) := by
  let := W.free_torsionEnvelope hn ξ
  infer_instance

/-- The universal x-coordinate in the affine envelope. -/
noncomputable def torsionEnvelopeXCoord (n : ℤ) (ξ : R) : W.torsionEnvelope n ξ :=
  algebraMap (W.torsionEnvelopeX n ξ) (W.torsionEnvelope n ξ)
    (AdjoinRoot.root (W.multiplicationFiberPolynomial n ξ))

/-- The universal y-coordinate in the affine envelope. -/
noncomputable def torsionEnvelopeYCoord (n : ℤ) (ξ : R) : W.torsionEnvelope n ξ :=
  AdjoinRoot.root (W.torsionEnvelopeYPolynomial n ξ)

set_option backward.isDefEq.respectTransparency false in
/-- Algebra-valued coordinates on the affine fibre evaluate its finite free envelope. -/
noncomputable def torsionEnvelopeLift {S : Type*} [CommRing S] [Algebra R S]
    (n : ℤ) (ξ : R) (x y : S)
    (hx : aeval x (W.multiplicationFiberPolynomial n ξ) = 0)
    (hy : (W.map (algebraMap R S)).toAffine.Equation x y) :
    W.torsionEnvelope n ξ →ₐ[R] S := by
  let fx : W.torsionEnvelopeX n ξ →ₐ[R] S :=
    AdjoinRoot.liftAlgHom _ (Algebra.ofId R S) x hx
  refine AdjoinRoot.liftAlgHom _ fx y ?_
  have he := (W.map (algebraMap R S)).toAffine.equation_iff' x y |>.mp hy
  simp only [torsionEnvelopeYPolynomial, eval₂_map]
  simpa [Affine.polynomial, map, fx, eval₂_pow, add_mul,
    aeval_def, AdjoinRoot.algebraMap_eq, AdjoinRoot.liftAlgHom_root,
    AdjoinRoot.liftAlgHom_of, add_assoc] using he

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation sends the universal x-coordinate to the specified x-coordinate. -/
@[simp] theorem torsionEnvelopeLift_x {S : Type*} [CommRing S] [Algebra R S]
    (n : ℤ) (ξ : R) (x y : S)
    (hx : aeval x (W.multiplicationFiberPolynomial n ξ) = 0)
    (hy : (W.map (algebraMap R S)).toAffine.Equation x y) :
    W.torsionEnvelopeLift n ξ x y hx hy (W.torsionEnvelopeXCoord n ξ) = x := by
  simp [torsionEnvelopeLift, torsionEnvelopeXCoord, AdjoinRoot.algebraMap_eq]

/-- Evaluation sends the universal y-coordinate to the specified y-coordinate. -/
@[simp] theorem torsionEnvelopeLift_y {S : Type*} [CommRing S] [Algebra R S]
    (n : ℤ) (ξ : R) (x y : S)
    (hx : aeval x (W.multiplicationFiberPolynomial n ξ) = 0)
    (hy : (W.map (algebraMap R S)).toAffine.Equation x y) :
    W.torsionEnvelopeLift n ξ x y hx hy (W.torsionEnvelopeYCoord n ξ) = y := by
  simp [torsionEnvelopeLift, torsionEnvelopeYCoord]

/-- Maps out of the affine envelope are determined by its two coordinates. -/
@[ext] theorem torsionEnvelope_hom_ext {S : Type*} [CommRing S] [Algebra R S]
    (n : ℤ) (ξ : R) {f g : W.torsionEnvelope n ξ →ₐ[R] S}
    (hx : f (W.torsionEnvelopeXCoord n ξ) = g (W.torsionEnvelopeXCoord n ξ))
    (hy : f (W.torsionEnvelopeYCoord n ξ) = g (W.torsionEnvelopeYCoord n ξ)) : f = g := by
  apply AdjoinRoot.algHom_ext'
  · apply AdjoinRoot.algHom_ext
    exact hx
  · exact hy

/-- The universal x-coordinate satisfies the multiplication-fibre equation. -/
theorem torsionEnvelope_x_relation (n : ℤ) (ξ : R) :
    aeval (W.torsionEnvelopeXCoord n ξ) (W.multiplicationFiberPolynomial n ξ) = 0 := by
  change aeval ((IsScalarTower.toAlgHom R (W.torsionEnvelopeX n ξ)
    (W.torsionEnvelope n ξ)) (AdjoinRoot.root _)) _ = 0
  rw [aeval_algHom_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]

set_option backward.isDefEq.respectTransparency false in
/-- The universal coordinates satisfy the integral Weierstrass equation. -/
theorem torsionEnvelope_equation (n : ℤ) (ξ : R) :
    (W.map (algebraMap R (W.torsionEnvelope n ξ))).toAffine.Equation
      (W.torsionEnvelopeXCoord n ξ) (W.torsionEnvelopeYCoord n ξ) := by
  let Q := W.torsionEnvelopeYPolynomial n ξ
  let x := W.torsionEnvelopeXCoord n ξ
  let y := W.torsionEnvelopeYCoord n ξ
  have he := AdjoinRoot.eval₂_root Q
  change eval₂ (AdjoinRoot.of Q) y
    (W.toAffine.polynomial.map
      (aeval (AdjoinRoot.root (W.multiplicationFiberPolynomial n ξ))).toRingHom) = 0 at he
  rw [eval₂_map] at he
  rw [Affine.equation_iff']
  simp only [Affine.polynomial, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X,
    eval₂_C, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C, aeval_X,
    map_add, map_mul, map_pow] at he
  change y ^ 2 + algebraMap R (W.torsionEnvelope n ξ) W.a₁ * x * y +
    algebraMap R (W.torsionEnvelope n ξ) W.a₃ * y -
    (x ^ 3 + algebraMap R (W.torsionEnvelope n ξ) W.a₂ * x ^ 2 +
      algebraMap R (W.torsionEnvelope n ξ) W.a₄ * x +
      algebraMap R (W.torsionEnvelope n ξ) W.a₆) = 0
  change y ^ 2 + (algebraMap R (W.torsionEnvelope n ξ) W.a₁ * x +
    algebraMap R (W.torsionEnvelope n ξ) W.a₃) * y -
    (x ^ 3 + algebraMap R (W.torsionEnvelope n ξ) W.a₂ * x ^ 2 +
      algebraMap R (W.torsionEnvelope n ξ) W.a₄ * x +
      algebraMap R (W.torsionEnvelope n ξ) W.a₆) = 0 at he
  linear_combination he

set_option backward.isDefEq.respectTransparency false in
/-- Evaluating the affine envelope gives exactly the pairs satisfying its two
coordinate equations, over arbitrary algebras including nonreduced ones. -/
noncomputable def torsionEnvelopePointsEquiv (S : Type*) [CommRing S] [Algebra R S]
    (n : ℤ) (ξ : R) :
    (W.torsionEnvelope n ξ →ₐ[R] S) ≃
      {xy : S × S // aeval xy.1 (W.multiplicationFiberPolynomial n ξ) = 0 ∧
        (W.map (algebraMap R S)).toAffine.Equation xy.1 xy.2} where
  toFun f := ⟨(f (W.torsionEnvelopeXCoord n ξ), f (W.torsionEnvelopeYCoord n ξ)), by
    constructor
    · rw [aeval_algHom_apply, W.torsionEnvelope_x_relation, map_zero]
    · have he := (W.torsionEnvelope_equation n ξ).map f.toRingHom
      have hc : f.toRingHom.comp (algebraMap R (W.torsionEnvelope n ξ)) =
          algebraMap R S := RingHom.ext f.commutes
      dsimp only [Affine.map, toAffine] at he
      rw [map_map, hc] at he
      exact he⟩
  invFun xy := W.torsionEnvelopeLift n ξ xy.val.1 xy.val.2 xy.property.1 xy.property.2
  left_inv f := W.torsionEnvelope_hom_ext n ξ
    (W.torsionEnvelopeLift_x n ξ _ _ _ _) (W.torsionEnvelopeLift_y n ξ _ _ _ _)
  right_inv xy := by
    apply Subtype.ext
    exact Prod.ext (W.torsionEnvelopeLift_x n ξ _ _ _ _)
      (W.torsionEnvelopeLift_y n ξ _ _ _ _)

section Field
variable {k : Type*} [Field k] [DecidableEq k] (E : WeierstrassCurve k)

/-- Above the abscissa of a nonzero two-torsion point, the affine envelope
has exactly the points of that multiplication fibre, with no sign ambiguity. -/
theorem isRoot_multiplicationFiberPolynomial_iff_nsmul_eq_two_torsion
    {x y ξ η : k} (h : E.toAffine.Nonsingular x y)
    (hT : E.toAffine.Nonsingular ξ η)
    (htwo : 2 • Affine.Point.some ξ η hT = 0) (n : ℕ) :
    (E.multiplicationFiberPolynomial n ξ).IsRoot x ↔
      n • Affine.Point.some x y h = Affine.Point.some ξ η hT := by
  rw [E.isRoot_multiplicationFiberPolynomial_iff h n ξ]
  constructor
  · rintro ⟨hne, hx⟩
    have he : (n • Affine.Point.some x y h).xRep =
        (Affine.Point.some ξ η hT).xRep := by
      generalize hQ : n • Affine.Point.some x y h = Q at *
      cases Q with
      | zero => exact (hne rfl).elim
      | some a b hab =>
        change a = ξ at hx
        simp only [Affine.Point.xRep_some, hx]
    rcases Affine.Point.eq_or_eq_neg_of_xRep_eq_xRep he with he | he
    · exact he
    · have hneg : -Affine.Point.some ξ η hT = Affine.Point.some ξ η hT :=
        neg_eq_of_add_eq_zero_left (by simpa only [two_nsmul] using htwo)
      exact he.trans hneg
  · intro he
    rw [he]
    exact ⟨Affine.Point.some_ne_zero hT, rfl⟩

/-- Every odd-torsion point, including infinity, becomes an affine point of
the finite envelope after translation by a nonzero two-torsion point. -/
theorem exists_affine_odd_torsion_translate {n : ℕ} (hn : Odd n)
    {ξ η : k} (hT : E.toAffine.Nonsingular ξ η)
    (htwo : 2 • Affine.Point.some ξ η hT = 0)
    (P : E.toAffine.Point) (hP : n • P = 0) :
    ∃ (x y : k) (h : E.toAffine.Nonsingular x y),
      P + Affine.Point.some ξ η hT = Affine.Point.some x y h ∧
        (E.multiplicationFiberPolynomial n ξ).IsRoot x := by
  have hm : n • (P + Affine.Point.some ξ η hT) = Affine.Point.some ξ η hT := by
    rw [nsmul_add, hP, odd_nsmul_of_two_nsmul_eq_zero hn htwo, zero_add]
  have hz := ne_zero_of_nsmul_eq_nonzero (Affine.Point.some_ne_zero hT) hm
  generalize hQ : P + Affine.Point.some ξ η hT = Q at *
  cases Q with
  | zero => exact (hz rfl).elim
  | some x y h =>
    exact ⟨x, y, h, rfl,
      (E.isRoot_multiplicationFiberPolynomial_iff_nsmul_eq_two_torsion h hT htwo n).mpr hm⟩

end Field

end WeierstrassCurve
