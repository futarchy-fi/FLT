/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.Algebra.CharP.Algebra

/-!
# Integral cyclotomic coordinates for arithmetic generators

The monic cyclotomic quotient over the integers is finite free of positive
rank. Its coordinate is a primitive root in the integral domain before any
specialization; subsequent reductions may identify powers with multiplicity.
-/

@[expose] public noncomputable section

open Polynomial

namespace FLT.Mazur.IntegralCyclotomicCoordinates

variable (n : ℕ) [NeZero n]

/-- The integral coordinate ring adjoining a cyclotomic generator. -/
abbrev Coordinate := AdjoinRoot (cyclotomic n ℤ)

/-- The integral cyclotomic ring is a domain. -/
instance coordinate_isDomain : IsDomain (Coordinate n) :=
  AdjoinRoot.isDomain_of_prime (irreducible_iff_prime.mp
    (cyclotomic.irreducible (NeZero.pos n)))

/-- Integer scalars embed in the monic positive-degree cyclotomic quotient. -/
theorem scalars_injective : Function.Injective (algebraMap ℤ (Coordinate n)) :=
  AdjoinRoot.of.injective_of_monic_of_degree_pos (cyclotomic.monic n ℤ)
    (degree_cyclotomic_pos n ℤ (NeZero.pos n))

instance coordinate_charZero : CharZero (Coordinate n) :=
  charZero_of_injective_algebraMap (scalars_injective n)

/-- The original polynomial coordinate in the integral cyclotomic quotient. -/
def root : Coordinate n := AdjoinRoot.root (cyclotomic n ℤ)

/-- The integral coordinate is primitive before passing to possibly nonreduced tests. -/
theorem primitive : IsPrimitiveRoot (root n) n := by
  apply (isRoot_cyclotomic_iff_charZero (NeZero.pos n)).mp
  have h := AdjoinRoot.isRoot_root (cyclotomic n ℤ)
  rwa [map_cyclotomic] at h

/-- The coordinate satisfies the nth-power relation integrally. -/
theorem root_pow : root n ^ n = 1 := (primitive n).pow_eq_one

/-- Its invertibility is retained under every ring specialization. -/
def rootUnit : (Coordinate n)ˣ := Units.ofPowEqOne _ n (root_pow n) (NeZero.ne n)

/-- The integral cover has the explicit Euler-totient basis. -/
def basis : Module.Basis (Fin n.totient) ℤ (Coordinate n) :=
  ((AdjoinRoot.powerBasis' (cyclotomic.monic n ℤ)).basis).reindex
    (finCongr (natDegree_cyclotomic n ℤ))

/-- The cover degree is positive for every positive root order. -/
theorem rank_pos : 0 < n.totient := Nat.totient_pos.mpr (NeZero.pos n)

end FLT.Mazur.IntegralCyclotomicCoordinates
