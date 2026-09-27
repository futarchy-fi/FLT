/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.TorsionPairing
/-!
# Bilinearity of the torsion pairing

The principal point-addition divisor compares the torsion functions for T,
U and T+U. Pulling back its generator does not change a torsion translation
ratio, which proves second-variable additivity. Alternation, nondegeneracy
and Galois equivariance are separate obligations.
-/

@[expose] public section

open scoped nonZeroDivisors WeierstrassCurve.Affine
namespace WeierstrassCurve.Affine.FunctionField
variable {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F]
  (W : Affine F) [W.IsElliptic]
omit [IsAlgClosed F] [W.IsElliptic] in
/-- The point divisor [T] + [U] - [T+U] - [O] has a nonzero rational generator. -/
theorem exists_add_relation (T U : W.Point) :
    ∃ h : W.FunctionField, h ≠ 0 ∧
      FractionalIdeal.spanSingleton W.CoordinateRing⁰ h =
        (T.fractionalIdeal * U.fractionalIdeal / (T + U).fractionalIdeal :
          (FractionalIdeal W.CoordinateRing⁰ W.FunctionField)ˣ) := by
  apply (Point.exists_generator_iff _).mpr
  rw [map_div, map_mul, Point.mk_fractionalIdeal, Point.mk_fractionalIdeal,
    Point.mk_fractionalIdeal, map_add]
  simp

/-- The principal point-addition relation makes root ratios multiply in the second point. -/
theorem TorsionRoot.ratio_add {n : ℕ} (hn : n ≠ 0)
    {T U : W.Point} (r : TorsionRoot W n hn T) (s : TorsionRoot W n hn U)
    (t : TorsionRoot W n hn (T + U))
    (S : Point.torsionKernel W n) :
    translationPullback W S.val t.g / t.g =
      (translationPullback W S.val r.g / r.g) *
        (translationPullback W S.val s.g / s.g) := by
  obtain ⟨h, hh0, hh⟩ := exists_add_relation W T U
  have hf : FractionalIdeal.spanSingleton W.CoordinateRing⁰ (r.f * s.f) =
      FractionalIdeal.spanSingleton W.CoordinateRing⁰ (t.f * h ^ n) := by
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton,
      ← FractionalIdeal.spanSingleton_mul_spanSingleton, ← FractionalIdeal.spanSingleton_pow,
      r.hf, s.hf, t.hf, hh]
    have he : T.fractionalIdeal ^ n * U.fractionalIdeal ^ n =
        (T + U).fractionalIdeal ^ n *
          (T.fractionalIdeal * U.fractionalIdeal / (T + U).fractionalIdeal) ^ n := by
      simp only [div_pow, mul_pow]
      exact (mul_div_cancel ((T + U).fractionalIdeal ^ n)
        (T.fractionalIdeal ^ n * U.fractionalIdeal ^ n)).symm
    exact congrArg Units.val he
  have hp0 : nsmulPullback W n hn h ≠ 0 := (map_ne_zero _).mpr hh0
  have he := translation_ratio_eq_of_pullback_span_eq W hn
    (mul_ne_zero r.hg0 s.hg0) (mul_ne_zero t.hg0 hp0)
    (show (r.g * s.g) ^ n = nsmulPullback W n hn (r.f * s.f) by
      rw [mul_pow, map_mul, r.hg, s.hg])
    (show (t.g * nsmulPullback W n hn h) ^ n =
        nsmulPullback W n hn (t.f * h ^ n) by
      rw [mul_pow, map_mul, map_pow, t.hg]) hf S.val
  have hinv := congrArg (fun φ : W.FunctionField →ₐ[F] W.FunctionField => φ h)
    (translation_nsmulPullback_of_torsion W n hn S.val S.property)
  change translationPullback W S.val (nsmulPullback W n hn h) =
    nsmulPullback W n hn h at hinv
  rw [map_mul, map_mul, hinv, mul_div_mul_right _ _ hp0] at he
  rw [← he, mul_div_mul_comm]

/-- The torsion pairing is additive in the point defining its torsion function. -/
theorem torsionPairing_add_right {n : ℕ} (hn : n ≠ 0) (hchar : (n : F) ≠ 0)
    (S T U : Point.torsionKernel W n) :
    torsionPairing W hn hchar S (T + U) =
      torsionPairing W hn hchar S T + torsionPairing W hn hchar S U := by
  apply Additive.toMul.injective
  apply rootsOfUnity.coe_injective
  apply (algebraMap F W.FunctionField).injective
  change algebraMap F W.FunctionField
    ((torsionPairing W hn hchar S (T + U)).toMul.val : F) =
    algebraMap F W.FunctionField (((torsionPairing W hn hchar S T).toMul.val : F) *
      ((torsionPairing W hn hchar S U).toMul.val : F))
  rw [map_mul, torsionPairing_eq_ratio W hn hchar S (T + U)
      (chosenTorsionRoot W hn hchar (T + U)),
    torsionPairing_eq_ratio W hn hchar S T (chosenTorsionRoot W hn hchar T),
    torsionPairing_eq_ratio W hn hchar S U (chosenTorsionRoot W hn hchar U)]
  exact TorsionRoot.ratio_add W hn _ _ _ S

/-- The translation-ratio construction as a bilinear map to additive roots of unity. -/
noncomputable def torsionPairingBilinear {n : ℕ} (hn : n ≠ 0) (hchar : (n : F) ≠ 0) :
    Point.torsionKernel W n →+ Point.torsionKernel W n →+ Additive (rootsOfUnity n F) :=
  AddMonoidHom.mk' (fun S => AddMonoidHom.mk'
    (torsionPairing W hn hchar S) (torsionPairing_add_right W hn hchar S))
    (fun S T => AddMonoidHom.ext (fun U => torsionPairing_add_left W hn hchar S T U))

end WeierstrassCurve.Affine.FunctionField
