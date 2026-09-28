/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FontaineConvolutionLifting
public import FLT.GroupScheme.FontainePointFieldEmbedding

/-!
# Fontaine's embedding property for killed-by-three models

The compatible lifting theorem gives Fontaine's property for the full ring
of integers of the full point field at every precision above three halves.
The separate implication from this property to the strict different bound
is not needed here.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

/-- The full point field of any finite flat model killed by three satisfies
Fontaine's embedding property at every precision strictly above three halves. -/
theorem FF.fontaineProperty_localPointField (M : FF ℤ_[3] ℚ_[3])
    (hM : KilledBy 3 M) {m : ℚ} (hm : 3 / 2 < m) :
    FontaineProperty (ThreeAdicIntegers (LocalPointField M)) m := by
  apply M.fontaineProperty_localPointField_of_compatibleLifting hM hm
  intro E _ _ _ _ _ u
  exact M.exists_compatible_integral_point E hM hm u

end ThreeAdicPlan
