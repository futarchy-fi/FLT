/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FontaineCorrectedObstruction
public import FLT.GroupScheme.FontaineDifferentHypothesis
public import FLT.GroupScheme.FontaineModelProperty

/-!
# Fontaine's strict different bound for models killed by three

The compatible lifting theorem supplies Fontaine's property for the integral
closure in the full point field. This field is already finite Galois, so the
corrected obstruction applies directly, with the same normalization `v(3) = 1`.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

/-- Every finite flat model over the three-adic integers killed by three has
full point field with normalized different exponent strictly below three halves. -/
theorem fontaineDifferentBoundKilledThree : FontaineDifferentBoundKilledThree := by
  intro M hM
  apply normalizedDifferentExponentLtThreeHalvesOfFontaineProperty (LocalPointField M)
  intro m hm
  exact M.fontaineProperty_localPointField hM hm

end ThreeAdicPlan
