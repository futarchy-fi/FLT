/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicInfinitesimalKernelEquiv
public import FLT.Mazur.AdicCompletedInfinitesimalKernelMap

/-!
# Constructed equivalences of completed original degree-one kernels

Finite polynomial presentations and a formal target equivalence supply
both infinitesimal lifts. The explicit difference homotopies prove the
resulting kernel maps inverse; no lift or homotopy is an additional input.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicCompletedInfinitesimalKernelEquiv

open AdicCompletedInfinitesimalLift

universe u

set_option backward.isDefEq.respectTransparency false

variable {R A B ι κ : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Finite ι] [Finite κ]
  (P : Algebra.Generators R A ι) (Q : Algebra.Generators R B κ)
  [IsNoetherianRing P.Ring] [IsNoetherianRing Q.Ring]
  (I : Ideal A) (J : Ideal B) [I.IsMaximal] [J.IsMaximal]
  (e : AdicCompletion I A ≃ₐ[R] AdicCompletion J B)

/-- The polynomial presentation retains its Noetherian presenting ring. -/
local instance presentationNoetherian : IsNoetherianRing P.toExtension.Ring :=
  inferInstanceAs (IsNoetherianRing P.Ring)

attribute [local instance] AdicInfinitesimalKernelEquiv.forwardInverse
  AdicInfinitesimalKernelEquiv.reverseInverse

/-- Both constructed infinitesimal maps form an equivalence on completed original kernels. -/
def equiv : LinearEquiv e.toRingHom (σ' := e.symm.toRingHom)
    (LinearMap.ker (AdicCompletion.map I P.toExtension.cotangentComplex))
    (LinearMap.ker (AdicCompletion.map J Q.toExtension.cotangentComplex)) := by
  let _ := AdicCompletedInfinitesimalSpaceMap.targetNoetherian P
  let _ := AdicCompletedInfinitesimalSpaceMap.targetNoetherian Q
  let _ := AdicCompletedInfinitesimalSpaceMap.finiteSpace P
  let _ := AdicCompletedInfinitesimalSpaceMap.finiteSpace Q
  exact AdicInfinitesimalKernelEquiv.equiv P.toExtension Q.toExtension I J e
    (lift P Q.toExtension I J e) (lift Q P.toExtension J I e.symm)
    (AdicCompletedInfinitesimalHom.projection_lift P Q.toExtension I J e)
    (AdicCompletedInfinitesimalHom.projection_lift Q P.toExtension J I e.symm)

/-- The forward equivalence is exactly the previously constructed original kernel map. -/
theorem equiv_apply
    (x : LinearMap.ker (AdicCompletion.map I P.toExtension.cotangentComplex)) :
    equiv P Q I J e x = AdicCompletedInfinitesimalKernelMap.map P Q.toExtension I J e x := by
  rfl

/-- The inverse equivalence is the previously constructed map for the opposite formal lift. -/
theorem equiv_symm_apply
    (x : LinearMap.ker (AdicCompletion.map J Q.toExtension.cotangentComplex)) :
    (equiv P Q I J e).symm x =
      AdicCompletedInfinitesimalKernelMap.map Q P.toExtension J I e.symm x := by
  rfl

end FLT.Mazur.AdicCompletedInfinitesimalKernelEquiv
