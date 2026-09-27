/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.MultiplicationRootExistence
/-!
# Torsion pairing values from multiplication roots

Every torsion point admits root data. Translating its root by a torsion point
produces a root of unity independent of both chosen functions. These ratios
define a character in the translating point.
-/

@[expose] public section

open scoped nonZeroDivisors WeierstrassCurve.Affine
namespace WeierstrassCurve.Affine.FunctionField
variable {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F]
  (W : Affine F) [W.IsElliptic]
/-- A torsion function together with a nonzero exact root of its multiplication pullback. -/
def TorsionRoot (n : ℕ) (hn : n ≠ 0) (T : W.Point) :=
  {fg : W.FunctionField × W.FunctionField //
    FractionalIdeal.spanSingleton W.CoordinateRing⁰ fg.1 =
      (T.fractionalIdeal : FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^ n ∧
    fg.2 ≠ 0 ∧ fg.2 ^ n = nsmulPullback W n hn fg.1}

namespace TorsionRoot
variable {W} {n : ℕ} {hn : n ≠ 0} {T : W.Point}
/-- The rational torsion function underlying the chosen root. -/
def f (r : TorsionRoot W n hn T) : W.FunctionField := r.val.1
/-- The chosen exact root of the pulled-back torsion function. -/
def g (r : TorsionRoot W n hn T) : W.FunctionField := r.val.2
omit [DecidableEq F] in
/-- The torsion function generates the nth power of the point ideal. -/
theorem hf (r : TorsionRoot W n hn T) :
    FractionalIdeal.spanSingleton W.CoordinateRing⁰ r.f =
      (T.fractionalIdeal : FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^ n := r.property.1
omit [DecidableEq F] in
/-- The chosen multiplication root is nonzero. -/
theorem hg0 (r : TorsionRoot W n hn T) : r.g ≠ 0 := r.property.2.1
omit [DecidableEq F] in
/-- The chosen root has the prescribed nth power. -/
theorem hg (r : TorsionRoot W n hn T) : r.g ^ n = nsmulPullback W n hn r.f := r.property.2.2
end TorsionRoot

/-- Every torsion point has root data when n is invertible, including the origin. -/
theorem nonempty_torsionRoot {n : ℕ} (hn : n ≠ 0) (hchar : (n : F) ≠ 0)
    (T : W.Point) (hT : n • T = 0) : Nonempty (TorsionRoot W n hn T) := by
  cases T with
  | zero => exact ⟨⟨(1, 1), by simp [Point.fractionalIdeal], one_ne_zero, by simp⟩⟩
  | some x y h =>
    obtain ⟨f, hf0, hf⟩ := Point.exists_torsionFunction h n hT
    obtain ⟨g, hg0, hg⟩ := exists_pow_eq_nsmulPullback W hn hchar h hf0 hf
    refine ⟨⟨(algebraMap W.CoordinateRing W.FunctionField f, g), ?_, hg0, hg⟩⟩
    rw [Point.fractionalIdeal_some, CoordinateRing.XYIdeal'_eq,
      ← FractionalIdeal.coeIdeal_pow, hf, FractionalIdeal.coeIdeal_span_singleton]

omit [DecidableEq F] [W.IsElliptic] in
/-- A rational function whose positive power is constant is constant. -/
theorem exists_const_of_pow {n : ℕ} (hn : n ≠ 0) {g : W.FunctionField} {c : F}
    (h : g ^ n = algebraMap F W.FunctionField c) :
    ∃ d : F, algebraMap F W.FunctionField d = g := by
  apply IsAlgebraic.exists_algebraMap_eq
  apply IsAlgebraic.of_pow (Nat.pos_of_ne_zero hn)
  rw [h]
  exact isAlgebraic_algebraMap c

/-- Roots of pullbacks of generators of the same ideal have identical translation ratios. -/
theorem translation_ratio_eq_of_pullback_span_eq {n : ℕ} (hn : n ≠ 0)
    {f₁ f₂ g₁ g₂ : W.FunctionField} (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0)
    (h₁ : g₁ ^ n = nsmulPullback W n hn f₁)
    (h₂ : g₂ ^ n = nsmulPullback W n hn f₂)
    (hf : FractionalIdeal.spanSingleton W.CoordinateRing⁰ f₁ =
      FractionalIdeal.spanSingleton W.CoordinateRing⁰ f₂) (S : W.Point) :
    translationPullback W S g₁ / g₁ = translationPullback W S g₂ / g₂ := by
  obtain ⟨c, _, hc⟩ := exists_eq_const_mul_of_span_eq hf
  have hp : (g₂ / g₁) ^ n = algebraMap F W.FunctionField c := by
    rw [div_pow, h₁, h₂, hc, map_mul, AlgHom.commutes, mul_div_cancel_right₀]
    rw [← h₁]
    exact pow_ne_zero _ hg₁
  obtain ⟨d, hd⟩ := exists_const_of_pow W hn hp
  have hd0 : algebraMap F W.FunctionField d ≠ 0 := hd ▸ div_ne_zero hg₂ hg₁
  have he : g₂ = algebraMap F W.FunctionField d * g₁ := (div_eq_iff hg₁).mp hd.symm
  rw [he, map_mul, AlgHom.commutes, mul_div_mul_left _ _ hd0]

/-- A torsion translation ratio is represented by a ground-field nth root of unity. -/
theorem exists_rootOfUnity_ratio {n : ℕ} (hn : n ≠ 0)
    {f g : W.FunctionField} (hg0 : g ≠ 0) (hg : g ^ n = nsmulPullback W n hn f)
    (S : Point.torsionKernel W n) :
    ∃ c : rootsOfUnity n F, algebraMap F W.FunctionField (c.val : F) =
      translationPullback W S.val g / g := by
  obtain ⟨c, hc0, hcn, hc⟩ := exists_translation_ratio_of_pow_eq_pullback W n hn
    S.val S.property hg0 hg
  exact ⟨⟨Units.mk0 c hc0, (mem_rootsOfUnity _ _).mpr (Units.ext hcn)⟩, hc.symm⟩

/-- The root of unity representing the translation ratio of a multiplication root. -/
noncomputable def rootOfUnityRatio {n : ℕ} (hn : n ≠ 0)
    {f g : W.FunctionField} (hg0 : g ≠ 0) (hg : g ^ n = nsmulPullback W n hn f)
    (S : Point.torsionKernel W n) : rootsOfUnity n F :=
  (exists_rootOfUnity_ratio W hn hg0 hg S).choose

/-- The selected root of unity equals the rational translation ratio. -/
theorem rootOfUnityRatio_spec {n : ℕ} (hn : n ≠ 0)
    {f g : W.FunctionField} (hg0 : g ≠ 0) (hg : g ^ n = nsmulPullback W n hn f)
    (S : Point.torsionKernel W n) :
    algebraMap F W.FunctionField ((rootOfUnityRatio W hn hg0 hg S).val : F) =
      translationPullback W S.val g / g :=
  (exists_rootOfUnity_ratio W hn hg0 hg S).choose_spec

/-- Translation ratios of a multiplication root define a character of the torsion subgroup. -/
noncomputable def rootCharacter {n : ℕ} (hn : n ≠ 0)
    {f g : W.FunctionField} (hg0 : g ≠ 0) (hg : g ^ n = nsmulPullback W n hn f) :
    Point.torsionKernel W n →+ Additive (rootsOfUnity n F) where
  toFun S := Additive.ofMul (rootOfUnityRatio W hn hg0 hg S)
  map_zero' := by
    apply Additive.toMul.injective
    apply rootsOfUnity.coe_injective
    apply (algebraMap F W.FunctionField).injective
    change algebraMap F W.FunctionField ((rootOfUnityRatio W hn hg0 hg 0).val : F) =
      algebraMap F W.FunctionField 1
    rw [rootOfUnityRatio_spec]
    simp [translationPullback_zero, hg0]
  map_add' S R := by
    apply Additive.toMul.injective
    apply rootsOfUnity.coe_injective
    apply (algebraMap F W.FunctionField).injective
    change algebraMap F W.FunctionField ((rootOfUnityRatio W hn hg0 hg (S + R)).val : F) =
      algebraMap F W.FunctionField
        (((rootOfUnityRatio W hn hg0 hg S).val : F) *
          ((rootOfUnityRatio W hn hg0 hg R).val : F))
    rw [map_mul, rootOfUnityRatio_spec, rootOfUnityRatio_spec, rootOfUnityRatio_spec]
    exact translation_ratio_add_of_pow_eq_pullback W n hn S.val R.val R.property hg0 hg

/-- The translation ratio is independent of the torsion function and its chosen root. -/
theorem TorsionRoot.ratio_eq {n : ℕ} {hn : n ≠ 0} {T : W.Point}
    (r r' : TorsionRoot W n hn T) (S : W.Point) :
    translationPullback W S r.g / r.g = translationPullback W S r'.g / r'.g :=
  translation_ratio_eq_of_pullback_span_eq W hn r.hg0 r'.hg0 r.hg r'.hg
    (r.hf.trans r'.hf.symm) S

/-- Choose root data for each torsion point over the algebraically closed field. -/
noncomputable def chosenTorsionRoot {n : ℕ} (hn : n ≠ 0) (hchar : (n : F) ≠ 0)
    (T : Point.torsionKernel W n) : TorsionRoot W n hn T.val :=
  (nonempty_torsionRoot W hn hchar T.val T.property).some

/-- The torsion pairing value given by translating a multiplication root. -/
noncomputable def torsionPairing {n : ℕ} (hn : n ≠ 0) (hchar : (n : F) ≠ 0)
    (S T : Point.torsionKernel W n) : Additive (rootsOfUnity n F) :=
  let r := chosenTorsionRoot W hn hchar T
  rootCharacter W hn r.hg0 r.hg S

/-- Any root data for the second point compute the same pairing value. -/
theorem torsionPairing_eq_ratio {n : ℕ} (hn : n ≠ 0) (hchar : (n : F) ≠ 0)
    (S T : Point.torsionKernel W n) (r : TorsionRoot W n hn T.val) :
    algebraMap F W.FunctionField ((torsionPairing W hn hchar S T).toMul.val : F) =
      translationPullback W S.val r.g / r.g := by
  change algebraMap F W.FunctionField
    ((rootOfUnityRatio W hn (chosenTorsionRoot W hn hchar T).hg0
      (chosenTorsionRoot W hn hchar T).hg S).val : F) = _
  rw [rootOfUnityRatio_spec]
  exact TorsionRoot.ratio_eq W _ r S.val

/-- The torsion pairing is additive in its translating point. -/
theorem torsionPairing_add_left {n : ℕ} (hn : n ≠ 0) (hchar : (n : F) ≠ 0)
    (S S' T : Point.torsionKernel W n) :
    torsionPairing W hn hchar (S + S') T =
      torsionPairing W hn hchar S T + torsionPairing W hn hchar S' T :=
  map_add (rootCharacter W hn (chosenTorsionRoot W hn hchar T).hg0
    (chosenTorsionRoot W hn hchar T).hg) S S'
end WeierstrassCurve.Affine.FunctionField
