/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Relative derivations descending through an original equation ideal

A derivation annihilating an equation ideal descends to the actual quotient
algebra with values in any quotient module. The construction preserves
representatives and is unique, so it applies to arithmetic node equations.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.QuotientRelativeDerivation

variable {R A N : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (I : Ideal A) [AddCommGroup N] [Module R N] [Module A N]
  [Module (A ⧸ I) N] [IsScalarTower A (A ⧸ I) N]
  (d : Derivation R A N) (hd : ∀ a ∈ I, d a = 0)

/-- Descend a relative derivation that annihilates the original equation ideal. -/
def lift : Derivation R (A ⧸ I) N where
  toFun := Quotient.lift d (by
    intro a b hab
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact hd (a - b) (Ideal.Quotient.eq.mp (Quotient.sound hab)))
  map_add' a b := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact d.map_add a b
  map_smul' r a := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact d.map_smul r a
  map_one_eq_zero' := d.map_one_eq_zero
  leibniz' a b := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    change d (a * b) = algebraMap A (A ⧸ I) a • d b + algebraMap A (A ⧸ I) b • d a
    rw [algebraMap_smul, algebraMap_smul, d.leibniz]

/-- The descended derivation retains its value on each original representative. -/
@[simp] theorem lift_mk (a : A) : lift I d hd (Ideal.Quotient.mk I a) = d a := rfl

/-- Values on original representatives uniquely determine a quotient derivation. -/
theorem lift_unique (e : Derivation R (A ⧸ I) N)
    (he : ∀ a, e (Ideal.Quotient.mk I a) = d a) : e = lift I d hd := by
  ext a : 1
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact he a

end FLT.Mazur.QuotientRelativeDerivation
