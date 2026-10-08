/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ReesModuleBaseChange

/-!
# Chart scalars inside the relative Rees action

The relative tensor action extends the original coefficient-ring action.
This scalar tower allows chart-linear localization to be upgraded to
localization over the relative tensor ring.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.Rees

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module S M] (I : Ideal R)

/-- Chart constants act on the relative model by their original scalar action. -/
lemma relativeModule_algebraMap_smul (s : S) (m : extendedModule (S := S) (M := M) I) :
    let _ := relativeModule (S := S) (M := M) I
    Algebra.algebraMap S (S ⊗[R] reesAlgebra I) s • m = s • m := by
  let _ := relativeModule (S := S) (M := M) I
  change relativeMap I (Algebra.algebraMap S (S ⊗[R] reesAlgebra I) s) • m = s • m
  rw [(relativeMap I).commutes]
  exact algebraMap_smul _ _ _

/-- The relative Rees action retains the original chart scalar tower. -/
instance relativeModule_scalarTower :
    let _ := relativeModule (S := S) (M := M) I
    IsScalarTower S (S ⊗[R] reesAlgebra I) (extendedModule (S := S) (M := M) I) := by
  let _ := relativeModule (S := S) (M := M) I
  exact IsScalarTower.of_algebraMap_smul (relativeModule_algebraMap_smul I)

end FLT.Mazur.Rees
