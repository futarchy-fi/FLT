/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ConstantCyclicGroup

/-!
# A generator of the constant cyclic group scheme

The component sections are powers of the section indexed by one. The powers
are taken in the actual group of scheme sections over the base.
-/

open CategoryTheory Limits AlgebraicGeometry MonObj MonoidalCategory CartesianMonoidalCategory
@[expose] public noncomputable section
namespace FLT.Mazur.ConstantCyclicGenerator
universe u
variable (S : Scheme.{u}) (n : ℕ) [NeZero n]
open ConstantCyclicGroup

/-- Component zero is the identity section. -/
theorem component_zero : component S n 0 = (1 : 𝟙_ (Over S) ⟶ model S n) := by
  change component S n 0 = η[𝟙_ (Over S)] ≫ component S n 0
  simp

/-- Adding indices multiplies the corresponding scheme sections. -/
theorem component_add (i j : ZMod n) :
    component S n (i + j) = component S n i * component S n j := by
  change _ = lift (component S n i) (component S n j) ≫ multiplication S n
  rw [← Category.id_comp (component S n i), ← Category.id_comp (component S n j),
    lift_component_multiplication]
  simp

/-- The natural-number component is a power of component one. -/
theorem component_natCast (k : ℕ) : component S n (k : ZMod n) = component S n 1 ^ k := by
  induction k with
  | zero => simpa using component_zero S n
  | succ k ih => rw [Nat.cast_add, Nat.cast_one, component_add, ih, pow_succ]

/-- Each component is a power with exponent in Fin n. -/
theorem component_pow (i : Fin n) :
    component S n (ZMod.finEquiv n i) = component S n 1 ^ i.val := by
  rw [← component_natCast]
  congr 1
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => exact (ZMod.natCast_zmod_val (n := n + 1) i).symm
end FLT.Mazur.ConstantCyclicGenerator
