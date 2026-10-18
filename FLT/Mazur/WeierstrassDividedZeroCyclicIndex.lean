/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCyclicSeed

/-!
# The concrete five-node cycle in standard polygon indices

The standard variable-smoothing polygon connects each left branch to the
preceding index. This enumeration preserves the proved source orientation.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth

/-- The enumeration whose predecessor is the concrete oriented cyclic successor. -/
def zeroCyclicIndex : Fin 5 ≃ ZeroCyclicVertex where
  toFun i := match i.val with
    | 0 => .terminal
    | 1 => .retained false
    | 2 => .initial false
    | 3 => .initial true
    | _ => .retained true
  invFun
    | .terminal => 0
    | .retained false => 1
    | .initial false => 2
    | .initial true => 3
    | .retained true => 4
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by rintro (_ | (_ | _) | (_ | _)) <;> rfl

/-- Every standard predecessor edge is precisely the concrete cyclic edge. -/
theorem zeroCyclicIndex_preceding (i : Fin 5) :
    zeroCyclicIndex ((finRotate 5).symm i) = zeroCyclicSuccessor (zeroCyclicIndex i) := by
  fin_cases i <;> rfl

/-- The inverse enumeration carries the concrete successor to the standard predecessor. -/
theorem zeroCyclicIndex_symm_successor (i : ZeroCyclicVertex) :
    zeroCyclicIndex.symm (zeroCyclicSuccessor i) = (finRotate 5).symm (zeroCyclicIndex.symm i) := by
  apply zeroCyclicIndex.injective
  rw [Equiv.apply_symm_apply, zeroCyclicIndex_preceding, Equiv.apply_symm_apply]

end FLT.Mazur.WeierstrassDividedDepth
