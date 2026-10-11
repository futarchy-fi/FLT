/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalizedCotangentFieldRank
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Cotangent fibers at primes below a localization center

A residue field at a prime below the localization center receives that local
ring. A rank computation on its punctured field points therefore computes the
original affine differential fiber.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.LocalizedPrimeCotangentRank

set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

universe u

variable (R A L : Type u) [CommRing R] [CommRing A] [CommRing L]
  [Algebra R A] [Algebra A L] [Algebra R L] [IsScalarTower R A L]
  (m : Ideal A) [m.IsPrime] [IsLocalization.AtPrime L m]

/-- A punctured local rank calculation computes every affine cotangent fiber below its center. -/
theorem finrank_eq (t : A) (d : ℕ)
    (hr : ∀ (B : Type u) [Field B] [Algebra L B],
      IsUnit (algebraMap L B (algebraMap A L t)) →
      Module.finrank B (B ⊗[L] Ω[L⁄R]) = d)
    (p : Ideal A) [p.IsPrime] (hp : p ≤ m) (ht : t ∉ p) :
    Module.finrank p.ResidueField (p.ResidueField ⊗[A] Ω[A⁄R]) = d := by
  have hu : ∀ a : m.primeCompl, IsUnit (algebraMap A p.ResidueField a) := by
    intro a
    exact isUnit_iff_ne_zero.mpr fun ha ↦ a.property (hp
      (Ideal.algebraMap_residueField_eq_zero.mp ha))
  let g : L →+* p.ResidueField := IsLocalization.lift hu
  let _ := g.toAlgebra
  let _ : IsScalarTower A L p.ResidueField :=
    IsScalarTower.of_algebraMap_eq' (by
      ext a
      exact (IsLocalization.lift_eq (S := L) hu a).symm)
  let _ : Algebra.FormallyEtale A L :=
    Algebra.FormallyEtale.of_isLocalization m.primeCompl
  rw [LocalizedCotangentFieldRank.finrank_eq R A L p.ResidueField]
  apply hr
  rw [← IsScalarTower.algebraMap_apply A L p.ResidueField]
  exact isUnit_iff_ne_zero.mpr (mt Ideal.algebraMap_residueField_eq_zero.mp ht)

end FLT.Mazur.LocalizedPrimeCotangentRank
