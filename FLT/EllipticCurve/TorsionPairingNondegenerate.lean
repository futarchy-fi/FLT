/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.MultiplicationDegree
public import FLT.EllipticCurve.TorsionPairingAlternating
public import FLT.EllipticCurve.TorsionPairingDescent
public import Mathlib.FieldTheory.Galois.Basic
/-!
# Descent and nondegeneracy of the torsion pairing

There are n² distinct translations fixing the multiplication image, whose
index is at most n². Galois theory identifies this image with their fixed
field. The descent criterion then proves nondegeneracy.
-/

@[expose] public section

open IntermediateField
open scoped WeierstrassCurve.Affine
namespace WeierstrassCurve.Affine.FunctionField
variable {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F]
  (W : Affine F) [W.IsElliptic]
/-- Translation by a torsion point fixes the multiplication image. -/
noncomputable def torsionTranslation {n : ℕ} (hn : n ≠ 0)
    (S : Point.torsionKernel W n) :
    W.FunctionField ≃ₐ[(nsmulPullback W n hn).fieldRange] W.FunctionField where
  __ := (translationEquiv W S.val).toRingEquiv
  commutes' c := by
    obtain ⟨f, hf⟩ := c.property
    change translationPullback W S.val c.val = c.val
    rw [← hf]
    exact congrArg (fun φ : W.FunctionField →ₐ[F] W.FunctionField => φ f)
      (translation_nsmulPullback_of_torsion W n hn S.val S.property)
/-- The torsion subgroup acts by automorphisms over the multiplication image. -/
noncomputable def torsionTranslationHom {n : ℕ} (hn : n ≠ 0) :
    Multiplicative (Point.torsionKernel W n) →*
      (W.FunctionField ≃ₐ[(nsmulPullback W n hn).fieldRange] W.FunctionField) where
  toFun S := torsionTranslation W hn S.toAdd
  map_one' := by
    ext f
    exact congrArg (fun φ : W.FunctionField →ₐ[F] W.FunctionField => φ f)
      (translationPullback_zero W)
  map_mul' S T := by
    ext f
    exact (congrArg (fun φ : W.FunctionField →ₐ[F] W.FunctionField => φ f)
      (translationPullback_add W S.toAdd.val T.toAdd.val)).symm

/-- Distinct torsion points induce distinct translation automorphisms. -/
theorem torsionTranslationHom_injective {n : ℕ} (hn : n ≠ 0) :
    Function.Injective (torsionTranslationHom W hn) := by
  intro S T he
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  apply Point.map_injective (W' := W) (f := Algebra.ofId F W.FunctionField)
  have hh : translationPullback W S.toAdd.val = translationPullback W T.toAdd.val := by
    apply AlgHom.ext
    intro f
    exact congrArg (fun φ : W.FunctionField ≃ₐ[(nsmulPullback W n hn).fieldRange]
      W.FunctionField => φ f) he
  have hp := congrArg (fun φ : W.FunctionField →ₐ[F] W.FunctionField =>
    Point.map (W' := W) φ (genericPoint W)) hh
  rw [translationPullback_genericPoint, translationPullback_genericPoint] at hp
  exact add_left_cancel hp

/-- Every function fixed by all torsion translations descends through multiplication. -/
theorem invariantFunction_descends {n : ℕ} (hn : n ≠ 0) (hchar : (n : F) ≠ 0)
    (g : W.FunctionField)
    (hg : ∀ S : Point.torsionKernel W n, translationPullback W S.val g = g) :
    ∃ f, nsmulPullback W n hn f = g := by
  let M := (nsmulPullback W n hn).fieldRange
  let H := (torsionTranslationHom W hn).range
  have : FiniteDimensional M W.FunctionField :=
    Module.finite_of_finrank_pos (finrank_nsmulPullback_bounds W n hn).1
  have hcard : Nat.card H = n ^ 2 := by
    rw [Nat.card_congr (MonoidHom.ofInjective (torsionTranslationHom_injective W hn)).toEquiv.symm]
    exact Point.card_torsionKernel W hchar
  have hfixed : fixedField H = (⊥ : IntermediateField M W.FunctionField) := by
    apply (eq_of_le_of_finrank_le' bot_le ?_).symm
    rw [finrank_bot', finrank_fixedField_eq_card, hcard]
    exact (finrank_nsmulPullback_bounds W n hn).2
  have hmem : g ∈ fixedField H := by
    rw [mem_fixedField_iff]
    rintro _ ⟨S, rfl⟩
    exact hg S.toAdd
  rw [hfixed, mem_bot] at hmem
  obtain ⟨c, hc⟩ := hmem
  obtain ⟨f, hf⟩ := c.property
  exact ⟨f, hf.trans hc⟩
/-- The torsion pairing is nondegenerate in its second argument. -/
theorem torsionPairing_right_nondegenerate {n : ℕ} (hn : n ≠ 0)
    (hchar : (n : F) ≠ 0) (T : Point.torsionKernel W n)
    (hT : ∀ S, torsionPairing W hn hchar S T = 0) : T = 0 :=
  torsionPairing_right_nondegenerate_of_descent W hn hchar
    (invariantFunction_descends W hn hchar) T hT

/-- The torsion pairing is nondegenerate in its first argument. -/
theorem torsionPairing_left_nondegenerate {n : ℕ} (hn : n ≠ 0)
    (hchar : (n : F) ≠ 0) (T : Point.torsionKernel W n)
    (hT : ∀ S, torsionPairing W hn hchar T S = 0) : T = 0 := by
  apply torsionPairing_right_nondegenerate W hn hchar T
  intro S
  rw [torsionPairing_swap, hT, neg_zero]
end WeierstrassCurve.Affine.FunctionField
