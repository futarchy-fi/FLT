/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CyclicPeriodicComplex
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic

/-!
# Periodic homology and cyclic cohomology

The even and odd homologies of the two-cycle recover the norm/difference
quotients and hence every positive even and odd cyclic cohomology group.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open CategoryTheory Rep.FiniteCyclicGroup

variable {k G : Type} [CommRing k] [CommGroup G] [Fintype G]
  (A : Rep k G) (g : G)

/-- The even periodic homology is the norm-then-difference quotient. -/
def cyclicPeriodicEvenIso :
    (cyclicPeriodicComplex A g).homology false ≅ (normHomCompSub A g).homology :=
  ShortComplex.homologyMapIso ((cyclicPeriodicComplex A g).isoSc' true false true
    (cyclicPeriodicShape.prev_eq' rfl) (cyclicPeriodicShape.next_eq' rfl))

/-- The odd periodic homology is the difference-then-norm quotient. -/
def cyclicPeriodicOddIso :
    (cyclicPeriodicComplex A g).homology true ≅ (subCompNormHom A g).homology :=
  ShortComplex.homologyMapIso ((cyclicPeriodicComplex A g).isoSc' false true false
    (cyclicPeriodicShape.prev_eq' rfl) (cyclicPeriodicShape.next_eq' rfl))

/-- Comparison with every positive even cyclic cohomology group. -/
def cyclicPeriodicGroupEvenIso (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (i : ℕ) [NeZero i] (hi : Even i) :
    groupCohomology A i ≅ (cyclicPeriodicComplex A g).homology false :=
  groupCohomologyIsoEven A g hg i hi ≪≫ (cyclicPeriodicEvenIso A g).symm

/-- Comparison with every odd cyclic cohomology group. -/
def cyclicPeriodicGroupOddIso (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (i : ℕ) (hi : Odd i) :
    groupCohomology A i ≅ (cyclicPeriodicComplex A g).homology true :=
  groupCohomologyIsoOdd A g hg i hi ≪≫ (cyclicPeriodicOddIso A g).symm

end LocalClassFieldTheory
