/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicCompletedInfinitesimalKernelEquiv
public import FLT.Mazur.AdicPresentationFirstCotangent

/-!
# Completed original first cotangent homology under a formal equivalence

Constructed infinitesimal lifts and their proved difference homotopies
identify completed ORIGINAL H1. Presentation independence is applied only
to the original polynomial presentations, before completing their kernels.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicCompletedFirstCotangentEquiv

universe u

set_option backward.isDefEq.respectTransparency false

variable {R A B ι κ : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Finite ι] [Finite κ]
  [Algebra.FinitePresentation R A] [Algebra.FinitePresentation R B]
  [IsNoetherianRing A] [IsNoetherianRing B]
  (P : Algebra.Generators R A ι) (Q : Algebra.Generators R B κ)
  [IsNoetherianRing P.Ring] [IsNoetherianRing Q.Ring]
  (I : Ideal A) (J : Ideal B) [I.IsMaximal] [J.IsMaximal]
  (e : AdicCompletion I A ≃ₐ[R] AdicCompletion J B)

attribute [local instance] AdicInfinitesimalKernelEquiv.forwardInverse
  AdicInfinitesimalKernelEquiv.reverseInverse
  AdicCompletedInfinitesimalKernelEquiv.presentationNoetherian

attribute [local irreducible] AdicPresentationFirstCotangent.equiv
  AdicCompletedInfinitesimalKernelEquiv.equiv

/-- Formal equivalence identifies the completed original first cotangent homology modules. -/
def equiv : LinearEquiv e.toRingHom (σ' := e.symm.toRingHom)
    (AdicCompletion I (Algebra.H1Cotangent R A))
    (AdicCompletion J (Algebra.H1Cotangent R B)) :=
  ((AdicPresentationFirstCotangent.equiv P I).trans
    (AdicCompletedInfinitesimalKernelEquiv.equiv P Q I J e)).trans
      (AdicPresentationFirstCotangent.equiv Q J).symm

/-- The H1 equivalence is computed by the constructed map on actual original degree-one cycles. -/
theorem equiv_kernel (x : AdicCompletion I (Algebra.H1Cotangent R A)) :
    AdicPresentationFirstCotangent.equiv Q J (equiv P Q I J e x) =
      AdicCompletedInfinitesimalKernelMap.map P Q.toExtension I J e
        (AdicPresentationFirstCotangent.equiv P I x) := by
  change AdicPresentationFirstCotangent.equiv Q J
    ((AdicPresentationFirstCotangent.equiv Q J).symm
      (AdicCompletedInfinitesimalKernelEquiv.equiv P Q I J e
        (AdicPresentationFirstCotangent.equiv P I x))) = _
  rw [LinearEquiv.apply_symm_apply, AdicCompletedInfinitesimalKernelEquiv.equiv_apply]

end FLT.Mazur.AdicCompletedFirstCotangentEquiv
