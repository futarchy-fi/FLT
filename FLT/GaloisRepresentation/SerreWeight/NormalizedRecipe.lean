/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Tactic

/-!
# The normalized odd-prime BDJ weight-set specification

This is the disjoint branch table in the proof of BDJ Theorem 3.17
(arXiv:0810.2106, pp. 29–30). A pair `(a,b)` denotes `det^a ⊗ Sym^(b-1)`.
The input is finite branch data, not an arithmetic predicate on representations.
In particular, no representation is asserted to supply these data here.
-/

@[expose] public section
namespace SerreWeightRecipe

/-- Weight labels before identifying determinant exponents modulo `p-1`. -/
abbrev Label := ℕ × ℕ

/-- The three possibilities for a reducible local extension. The exceptional
case requires whole-local cyclotomic ratio and a non-peu extension. -/
inductive ExtensionCase
  | split
  | nonsplit
  | cyclotomicTres
  deriving DecidableEq

/-- Normalized reducible branch data; no output weights are supplied as fields. -/
structure ReducibleInput (p : ℕ) where
  /-- The normalized upper inertia exponent. -/
  exponent : ℕ
  lower : 1 ≤ exponent
  upper : exponent ≤ p - 1
  /-- Splitting over the whole local group, or the exceptional extension case. -/
  extensionCase : ExtensionCase
  /-- The exceptional whole-local cyclotomic ratio has inertia exponent one. -/
  exceptionalExponent : extensionCase = .cyclotomicTres → exponent = 1

/-- The complete normalized reducible table, with the small-prime overlap
resolved before the general split branches. -/
def reducible (p : ℕ) (d : ReducibleInput p) : Finset Label :=
  if d.exponent = 1 then
    match d.extensionCase with
    | .cyclotomicTres => {(0, p)}
    | .split => if p = 3 then {(0, 3), (0, 1), (1, 3), (1, 1)}
        else {(0, p), (0, 1), (1, p - 2)}
    | .nonsplit => {(0, p), (0, 1)}
  else if d.exponent = p - 1 then {(0, p - 1)}
  else if d.extensionCase = .split then
    if d.exponent = p - 2 then {(0, p - 2), (p - 2, p), (p - 2, 1)}
    else {(0, d.exponent), (d.exponent, p - 1 - d.exponent)}
  else {(0, d.exponent)}

/-- The normalized niveau-two table. Its arithmetic use requires `1 ≤ b < p`. -/
def niveauTwo (p b : ℕ) : Finset Label := {(0, b), (b - 1, p + 1 - b)}

/-- Determinant twisting acts on labels modulo `p-1`. -/
def twist (p a : ℕ) (weights : Finset Label) : Finset Label :=
  weights.image fun w ↦ ((w.1 + a) % (p - 1), w.2)

/-- Scalar inertia uses the exponent `p-1`, independently of splitting. -/
theorem reducible_scalar {p : ℕ} (hp : 3 ≤ p) (d : ReducibleInput p)
    (hb : d.exponent = p - 1) : reducible p d = {(0, p - 1)} := by
  have hne : d.exponent ≠ 1 := by omega
  simp only [reducible, ite_eq_right hne, ite_eq_left hb]

/-- Nonsplit nonexceptional exponent-one extensions include both low weights. -/
theorem reducible_one_nonsplit {p : ℕ} (d : ReducibleInput p)
    (hb : d.exponent = 1) (he : d.extensionCase = .nonsplit) :
    reducible p d = {(0, p), (0, 1)} := by
  simp [reducible, hb, he]

/-- The tres branch does not include the weight-two label. -/
theorem reducible_tres {p : ℕ} (d : ReducibleInput p)
    (he : d.extensionCase = .cyclotomicTres) : reducible p d = {(0, p)} := by
  simp [reducible, d.exceptionalExponent he, he]

/-- At three, the split exponent-one branch has four labels. -/
theorem reducible_three_split (d : ReducibleInput 3)
    (hb : d.exponent = 1) (he : d.extensionCase = .split) :
    reducible 3 d = {(0, 3), (0, 1), (1, 3), (1, 1)} := by
  simp [reducible, hb, he]

/-- All weights returned by the reducible table have normalized dimensions. -/
theorem reducible_bounds {p : ℕ} (hp : 3 ≤ p) (d : ReducibleInput p)
    {w : Label} (hw : w ∈ reducible p d) : w.1 < p - 1 ∧ 1 ≤ w.2 ∧ w.2 ≤ p := by
  have hlo := d.lower
  have hhi := d.upper
  unfold reducible at hw
  split at hw
  · split at hw
    · simp only [Finset.mem_singleton] at hw
      subst w
      omega
    · split at hw <;> simp only [Finset.mem_insert, Finset.mem_singleton] at hw <;>
        rcases hw with rfl | rfl | rfl | rfl <;> simp_all <;> omega
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl <;> simp_all <;> omega
  · split at hw
    · simp only [Finset.mem_singleton] at hw
      subst w
      simp_all
      omega
    · split at hw
      · split at hw
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl | rfl <;> simp_all <;> omega
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl <;> simp_all <;> omega
      · simp only [Finset.mem_singleton] at hw
        subst w
        simp_all
        omega

end SerreWeightRecipe
