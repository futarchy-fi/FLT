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

end WeierstrassCurve
