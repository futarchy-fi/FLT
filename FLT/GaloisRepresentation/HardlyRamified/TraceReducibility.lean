/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Push

/-! # An elementary rank-two trace criterion for reducibility

The argument works over any field: a nonidentity matrix minus the identity has
rank one. Its trace pairing with the representation supplies a one-dimensional
quotient, contradicting irreducibility.
-/

@[expose] public section

namespace GaloisRepresentation.B5Inputs

open Module

/-- An orbit on which a nonzero functional transforms by a character rules out
irreducibility in dimension greater than one. Under irreducibility the identity
extends to the whole space, making the functional's kernel invariant. -/
private theorem not_irreducible_of_covector
    {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (hV : 1 < finrank k V)
    (ρ : Representation k G V) (χ : G →* k)
    (φ : V →ₗ[k] k) (hφ : φ ≠ 0) (v : V) (hv : v ≠ 0)
    (h : ∀ g, φ (ρ g v) = χ g * φ v) : ¬ ρ.IsIrreducible := by
  intro hirr
  let := hirr
  let N : Subrepresentation ρ :=
    { toSubmodule :=
        { carrier := {w | ∀ g, φ (ρ g w) = χ g * φ w}
          zero_mem' := by simp
          add_mem' := by intro x y hx hy g; simp [hx g, hy g, mul_add]
          smul_mem' := by intro c x hx g; simp [hx g, mul_left_comm] }
      apply_mem_toSubmodule := by
        intro g w hw a
        rw [← Module.End.mul_apply, ← map_mul, hw, hw, map_mul, mul_assoc] }
  have hN : N = ⊤ := (eq_bot_or_eq_top N).resolve_left (by
    intro hn
    have : v ∈ N := h
    rw [hn] at this
    exact hv this)
  have heq (g : G) (w : V) : φ (ρ g w) = χ g * φ w := by
    have hw : w ∈ N := by rw [hN]; trivial
    exact hw g
  let K : Subrepresentation ρ :=
    { toSubmodule := LinearMap.ker φ
      apply_mem_toSubmodule := by
        intro g w hw
        change φ (ρ g w) = 0
        rw [heq, LinearMap.mem_ker.mp hw, mul_zero] }
  rcases eq_bot_or_eq_top K with hk | hk
  · have hinj : Function.Injective φ := LinearMap.ker_eq_bot.mp (congrArg
      Subrepresentation.toSubmodule hk)
    have := LinearMap.finrank_le_finrank_of_injective hinj
    simp only [finrank_self] at this
    omega
  · apply hφ
    ext w
    have hw : w ∈ K := by rw [hk]; trivial
    exact hw

/-- In dimension two, `tr A = 1 + det A` means that `A - 1` is singular. -/
private theorem det_sub_one_eq_zero
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (hV : finrank k V = 2)
    (A : Module.End k V) (h : A.trace k V = 1 + A.det) : (A - 1).det = 0 := by
  let b := Module.finBasisOfFinrankEq k V hV
  rw [LinearMap.trace_eq_matrix_trace k b, ← LinearMap.det_toMatrix b] at h
  rw [← LinearMap.det_toMatrix b, map_sub, LinearMap.toMatrix_one]
  simp only [Matrix.det_fin_two, Matrix.trace, Matrix.diag, Fin.sum_univ_two,
    Matrix.sub_apply, Matrix.one_apply, Fin.isValue, Fin.zero_eq_one_iff, Fin.one_eq_zero_iff,
    Nat.reduceEqDiff, ↓reduceIte] at h ⊢
  linear_combination -h

/-- A two-dimensional representation whose trace is `1 + det` everywhere is
reducible. No assumption on the characteristic or on absolute irreducibility is
needed. -/
theorem not_isIrreducible_of_trace_eq_one_add_det
    {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (hV : finrank k V = 2)
    (ρ : Representation k G V)
    (htrace : ∀ g, (ρ g).trace k V = 1 + (ρ g).det) : ¬ ρ.IsIrreducible := by
  classical
  let χ : G →* k := LinearMap.det.comp ρ
  by_cases htriv : ∀ g, ρ g = 1
  · let b := Module.finBasisOfFinrankEq k V hV
    apply not_irreducible_of_covector (by omega) ρ (1 : G →* k)
      (b.coord 0) (by intro h; have := congrArg (fun f : V →ₗ[k] k => f (b 0)) h; simp at this)
      (b 0) (b.ne_zero 0)
    intro g
    simp [htriv]
  · push Not at htriv
    obtain ⟨g, hg⟩ := htriv
    let D := ρ g - 1
    have hD : D ≠ 0 := sub_ne_zero.mpr hg
    have hsing : D.det = 0 := det_sub_one_eq_zero hV _ (htrace g)
    have hrank : finrank k (LinearMap.range D) = 1 := by
      have hker := LinearMap.det_eq_zero_iff_ker_ne_bot.mp hsing
      have hdim := LinearMap.finrank_range_add_finrank_ker D
      have hkpos : 0 < finrank k (LinearMap.ker D) :=
        by simpa [pos_iff_ne_zero, Submodule.finrank_eq_zero] using hker
      have hrpos : 0 < finrank k (LinearMap.range D) :=
        by simpa [pos_iff_ne_zero, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] using hD
      omega
    -- Factor the rank-one difference as `w ↦ φ(w) • v`.
    obtain ⟨e⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one hrank
    let v : V := (e 1).val
    let φ : V →ₗ[k] k := e.symm.toLinearMap.comp D.rangeRestrict
    have hfactor : D = φ.smulRight v := by
      ext w
      change (D.rangeRestrict w).val = (φ w • e 1).val
      congr 1
      simp [φ, ← map_smul]
    have hv : v ≠ 0 := by
      intro hv
      have : e 1 = 0 := Subtype.ext hv
      have := e.injective (this.trans e.map_zero.symm)
      exact one_ne_zero this
    have hφ : φ ≠ 0 := by
      intro hφ
      apply hD
      rw [hfactor, hφ]
      simp
    apply not_irreducible_of_covector (by omega) ρ χ φ hφ v hv
    intro a
    -- `tr ((ρ(g) - 1) ρ(a)) = det ρ(a) * tr (ρ(g) - 1)`.
    have hpair : (D * ρ a).trace k V = χ a * D.trace k V := by
      dsimp [D, χ]
      rw [sub_mul, one_mul, map_sub, ← map_mul, htrace, map_sub,
        htrace, LinearMap.trace_one, hV]
      simp only [map_mul, Nat.cast_ofNat, htrace]
      ring
    rw [hfactor, LinearMap.trace_smulRight] at hpair
    have hcomp : φ.smulRight v * ρ a = (φ.comp (ρ a)).smulRight v := rfl
    rwa [hcomp, LinearMap.trace_smulRight] at hpair

end GaloisRepresentation.B5Inputs
