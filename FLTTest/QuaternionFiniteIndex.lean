/-
Copyright (c) 2026 FLT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT contributors
-/
module

import FLT.AutomorphicForm.QuaternionAlgebra.Basic

/-! Regression checks for quaternionic stabilizer finiteness and its axiom dependencies. -/

/--
info: 'IsQuaternionAlgebra.finiteRelIndex_of_compact_mod_scalars' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms IsQuaternionAlgebra.finiteRelIndex_of_compact_mod_scalars

/--
info: 'TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm.LevelStruct.isFiniteRelIndex_Δ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm.LevelStruct.isFiniteRelIndex_Δ
