/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.HopfTorsor
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import FLT.GroupScheme.RaynaudModelArithmetic

/-!
# Finite-flat p-divisible systems with étale generic fibre

A system is given by its finite flat levels and coherent inclusions and
reductions. Exactness is imposed on the actual coordinate maps; multiplication
factors through those maps. Height is measured by integral coordinate rank.
This is the level presentation, not a constructed fppf colimit or a period comparison.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan

/-- A finite-flat p-divisible system, including its level-zero term.
The defining conditions must be proved by each constructor. -/
structure PDivisibleSystem (R K : Type) [CommRing R] [Field K] [Algebra R K]
    [PerfectField K] [IsFractionRing R K] (p height : ℕ) [Fact p.Prime] where
  /-- The finite flat integral levels. -/
  level : ℕ → FF R K
  /-- Closed inclusions between ordered levels, contravariant on coordinates. -/
  inclusion : ∀ {m n : ℕ}, m ≤ n → ModelHom (level m) (level n)
  /-- The quotient reductions on these same levels. -/
  reduction : ∀ {m n : ℕ}, m ≤ n → ModelHom (level n) (level m)
  inclusion_refl : ∀ n, inclusion (le_refl n) = BialgHom.id R _
  reduction_refl : ∀ n, reduction (le_refl n) = BialgHom.id R _
  inclusion_comp : ∀ {l m n} (h : l ≤ m) (k : m ≤ n),
    (inclusion h).comp (inclusion k) = inclusion (h.trans k)
  reduction_comp : ∀ {l m n} (h : l ≤ m) (k : m ≤ n),
    (reduction k).comp (reduction h) = reduction (h.trans k)
  closed : ∀ {m n} (h : m ≤ n), Function.Surjective (inclusion h)
  faithfullyFlat : ∀ {m n} (h : m ≤ n),
    (reduction h).toAlgHom.toRingHom.FaithfullyFlat
  kernel : ∀ m n, HopfAlgebra.augmentationIdeal (reduction (Nat.le_add_left n m)) =
    RingHom.ker (inclusion (Nat.le_add_right m n)).toAlgHom.toRingHom
  inclusion_reduction : ∀ {m n} (h : m ≤ n),
    (inclusion h).comp (reduction h) = (level m).multiply (p ^ (n - m))
  reduction_inclusion : ∀ {m n} (h : m ≤ n),
    (reduction h).comp (inclusion h) = (level n).multiply (p ^ (n - m))
  killed : ∀ n (x : (level n).Points), p ^ n • x = 0
  rank : ∀ n, Module.finrank R (level n).CoordinateRing = p ^ (n * height)

end ThreeAdicPlan
