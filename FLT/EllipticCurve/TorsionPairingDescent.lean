/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.TorsionPairing
/-!
# Reducing nondegeneracy to invariant-function descent

If a multiplication root is itself a multiplication pullback, its point
ideal is principal, so its torsion point is the origin. Thus right
nondegeneracy follows once functions fixed by all torsion translations are
shown to lie in the multiplication image. That descent hypothesis remains
explicit; this module does not prove nondegeneracy unconditionally.
-/

@[expose] public section

open scoped nonZeroDivisors WeierstrassCurve.Affine
namespace WeierstrassCurve.Affine.FunctionField
variable {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F]
  (W : Affine F) [W.IsElliptic]
omit [DecidableEq F] in
/-- A torsion root that itself descends through multiplication belongs to the origin. -/
theorem TorsionRoot.point_eq_zero_of_isPullback {n : ℕ} (hn : n ≠ 0) {T : W.Point}
    (r : TorsionRoot W n hn T) (hdesc : ∃ h, nsmulPullback W n hn h = r.g) : T = 0 := by
  classical
  obtain ⟨h, hh⟩ := hdesc
  have hh0 : h ≠ 0 := by
    intro hz
    apply r.hg0
    rw [← hh, hz, map_zero]
  have hp : h ^ n = r.f := by
    apply (nsmulPullback W n hn).injective
    change nsmulPullback W n hn (h ^ n) = nsmulPullback W n hn r.f
    rw [map_pow, hh, r.hg]
  have hs : FractionalIdeal.spanSingleton W.CoordinateRing⁰ h =
      (T.fractionalIdeal : FractionalIdeal W.CoordinateRing⁰ W.FunctionField) := by
    apply CoordinateRing.fractionalIdeal_ext
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hh0) T.fractionalIdeal.ne_zero
    intro x y ht
    have he := congrArg (FractionalIdeal.count W.FunctionField
      (CoordinateRing.pointSpectrum ht)) r.hf
    rw [← hp, ← FractionalIdeal.spanSingleton_pow,
      FractionalIdeal.count_pow, FractionalIdeal.count_pow] at he
    exact mul_left_cancel₀ (show (n : ℤ) ≠ 0 by exact_mod_cast hn) he
  have hc := (Point.exists_generator_iff T.fractionalIdeal).mp ⟨h, hh0, hs⟩
  rw [Point.mk_fractionalIdeal] at hc
  apply Point.toClass_injective
  apply Additive.toMul.injective
  simpa using hc

/-- Descent of invariant functions implies right nondegeneracy of the torsion pairing. -/
theorem torsionPairing_right_nondegenerate_of_descent {n : ℕ} (hn : n ≠ 0)
    (hchar : (n : F) ≠ 0)
    (hdesc : ∀ g : W.FunctionField,
      (∀ S : Point.torsionKernel W n, translationPullback W S.val g = g) →
      ∃ h, nsmulPullback W n hn h = g)
    (T : Point.torsionKernel W n)
    (hT : ∀ S, torsionPairing W hn hchar S T = 0) : T = 0 := by
  let r := chosenTorsionRoot W hn hchar T
  apply Subtype.ext
  apply TorsionRoot.point_eq_zero_of_isPullback W hn r
  apply hdesc
  intro S
  have he := torsionPairing_eq_ratio W hn hchar S T r
  rw [hT] at he
  change algebraMap F W.FunctionField 1 = translationPullback W S.val r.g / r.g at he
  rw [map_one] at he
  exact (div_eq_one_iff_eq r.hg0).mp he.symm
end WeierstrassCurve.Affine.FunctionField
