/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.FiniteHomologyCard
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic

/-!
# The Herbrand cardinal equality for finite cyclic modules

For finite coefficients, the even and odd positive cohomology groups have
equal order. This is the finite-module input to the Herbrand quotient argument.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open CategoryTheory Rep.FiniteCyclicGroup

variable {k G : Type} [CommRing k] [CommGroup G]
  (A : Rep k G) [Finite A.V] (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)

/-- The two periodic homologies of a finite coefficient module have equal order. -/
theorem finiteCyclic_periodic_card [Fintype G] :
    Nat.card (normHomCompSub A g).homology = Nat.card (subCompNormHom A g).homology := by
  apply finite_periodic_homology_card A.norm.hom.toLinearMap
    (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap
  · exact congrArg ModuleCat.Hom.hom (normHomCompSub A g).zero
  · exact congrArg ModuleCat.Hom.hom (subCompNormHom A g).zero

variable [Finite G]

include hg

/-- Finite cyclic coefficients have equal even and odd positive cohomology orders. -/
theorem finiteCyclic_even_odd_card (i j : ℕ) [NeZero i] (hi : Even i) (hj : Odd j) :
    Nat.card (groupCohomology A i) = Nat.card (groupCohomology A j) := by
  let := Fintype.ofFinite G
  calc
    _ = Nat.card (normHomCompSub A g).homology := Nat.card_congr
      (groupCohomologyIsoEven A g hg i hi).toLinearEquiv.toEquiv
    _ = Nat.card (subCompNormHom A g).homology := finiteCyclic_periodic_card A g
    _ = _ := Nat.card_congr
      (groupCohomologyIsoOdd A g hg j hj).toLinearEquiv.toEquiv.symm

/-- The numerator and denominator in the finite-module Herbrand quotient agree. -/
theorem finiteCyclic_H2_card_eq_H1 :
    Nat.card (groupCohomology A 2) = Nat.card (groupCohomology A 1) :=
  finiteCyclic_even_odd_card A g hg 2 1 (by decide) (by decide)

/-- Finite coefficients give finite odd cohomology, using the actual periodic comparison. -/
theorem finiteCyclic_odd_finite (j : ℕ) (hj : Odd j) : Finite (groupCohomology A j) := by
  let := Fintype.ofFinite G
  let := shortComplex_homology_finite (subCompNormHom A g)
  exact Finite.of_equiv _
    (groupCohomologyIsoOdd A g hg j hj).toLinearEquiv.toEquiv.symm

/-- The Herbrand quotient of a finite cyclic coefficient module is one. -/
theorem finiteCyclic_herbrand_eq_one :
    (Nat.card (groupCohomology A 2) : ℚ) / Nat.card (groupCohomology A 1) = 1 := by
  let := finiteCyclic_odd_finite A g hg 1 (by decide)
  rw [finiteCyclic_H2_card_eq_H1 A g hg]
  exact div_self (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

end LocalClassFieldTheory
