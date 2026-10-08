/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ReesAlgebraBaseChange
public import Mathlib.RingTheory.Filtration

/-!
# Finite Rees modules over the relative algebra

The actual module of powers of an extended ideal is finite over the relative
Rees algebra when the coefficient module is finite over a Noetherian chart.
The action uses the proved surjection, not a finiteness assumption on the
chart over the original base.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.Rees

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module S M] (I : Ideal R)

/-- The ordinary Rees module of the extended ideal acting on the coefficient module. -/
abbrev extendedModule :=
  ((I.map (Algebra.algebraMap R S)).stableFiltration (⊤ : Submodule S M)).submodule

/-- The relative algebra acts through its original coefficientwise surjection. -/
@[instance_reducible]
def relativeModule : Module (S ⊗[R] reesAlgebra I) (extendedModule (S := S) (M := M) I) :=
  Module.compHom _ (relativeMap (S := S) I).toRingHom

/-- The relative scalar action is the scalar action of its image in the local Rees algebra. -/
lemma relativeModule_smul (r : S ⊗[R] reesAlgebra I) (m : extendedModule (S := S) (M := M) I) :
    let _ := relativeModule (S := S) (M := M) I
    r • m = relativeMap I r • m := rfl

variable [IsNoetherianRing S] [Module.Finite S M]

/-- The ordinary local Rees module is finite over the extended-ideal Rees algebra. -/
theorem extendedModule_finite :
    Module.Finite (reesAlgebra (I.map (Algebra.algebraMap R S)))
      (extendedModule (S := S) (M := M) I) := by
  apply Module.Finite.of_fg
  apply (Ideal.Filtration.submodule_fg_iff_stable _ (fun _ ↦ IsNoetherian.noetherian _)).mpr
  exact (I.map (Algebra.algebraMap R S)).stableFiltration_stable ⊤

/-- Finiteness over the relative algebra follows from the actual quotient comparison. -/
theorem relativeModule_finite :
    let _ := relativeModule (S := S) (M := M) I
    Module.Finite (S ⊗[R] reesAlgebra I) (extendedModule (S := S) (M := M) I) := by
  let _ := (relativeMap (S := S) I).toRingHom.toAlgebra
  let _ := relativeModule (S := S) (M := M) I
  let _ : IsScalarTower (S ⊗[R] reesAlgebra I)
      (reesAlgebra (I.map (Algebra.algebraMap R S))) (extendedModule (S := S) (M := M) I) :=
    ⟨fun r s m ↦ mul_smul (relativeMap I r) s m⟩
  let _ : Module.Finite (S ⊗[R] reesAlgebra I)
      (reesAlgebra (I.map (Algebra.algebraMap R S))) := relativeMap_finite I
  let _ := extendedModule_finite (S := S) (M := M) I
  exact Module.Finite.trans (reesAlgebra (I.map (Algebra.algebraMap R S))) _

end FLT.Mazur.Rees
