/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFlatDifferentials
public import FLT.GroupScheme.LocalPointField

/-!
# The local Fontaine bound as an explicit hypothesis

The proposition below is the missing strict local different bound for the
full field of geometric points of a finite flat model killed by three.
It is a proposition to be supplied to a reduction, not an axiom or a theorem
asserting that the bound has been proved. In particular it concerns the
integral closure in the point field, rather than the model's coordinate ring.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

/-- Fontaine's strict normalized different bound for finite flat models over
`ℤ_[3]` killed by three. The normalization is `v(3) = 1` and the point field
is the fixed field of the kernel of the action on all geometric points.
This named proposition is an explicit hypothesis, not an established bound. -/
def fontaine_different_bound_killed_three : Prop :=
  ∀ (M : FF ℤ_[3] ℚ_[3]), KilledBy 3 M →
    normalizedDifferentExponent (LocalPointField M) < (3 / 2 : ℚ)

end ThreeAdicPlan
