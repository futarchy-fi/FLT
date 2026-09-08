/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import FLT.Deformations.RepresentationTheory.GaloisRep
public import Mathlib.RepresentationTheory.Semisimple

/-!
# Chebotarev comparison for Galois representations

This is the shared statement-layer interface used by cyclic base change and the compatible-family
arguments.  It records the finite exceptional set, unramifiedness, equality of Frobenius
characteristic polynomials, and semisimplicity explicitly.  The proof is the classical
Chebotarev/Brauer–Nesbitt argument and is intentionally deferred.
-/

@[expose] public section

open NumberField

namespace CyclicBaseChange

universe uK uA uM uN

local notation "Ω" K => IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)

/-- Two semisimple continuous Galois representations with matching Frobenius characteristic
polynomials away from a finite set are isomorphic. -/
theorem exists_conjugating_equiv_of_charFrob_eq_outside
    {K : Type uK} [Field K] [NumberField K]
    {A : Type uA} [Field A] [TopologicalSpace A] [T2Space A]
    {M : Type uM} [AddCommGroup M] [Module A M] [Module.Free A M] [Module.Finite A M]
    {N : Type uN} [AddCommGroup N] [Module A N] [Module.Free A N] [Module.Finite A N]
    (rho : GaloisRep K A M) (rho' : GaloisRep K A N) (exceptional : Finset (Ω K))
    (hsemisimple : rho.toRepresentation.IsSemisimpleRepresentation)
    (hsemisimple' : rho'.toRepresentation.IsSemisimpleRepresentation)
    (hunramified : ∀ v, v ∉ exceptional →
      GaloisRep.IsUnramifiedAt rho v ∧ GaloisRep.IsUnramifiedAt rho' v)
    (hcharpoly : ∀ v, v ∉ exceptional → rho.charFrob v = rho'.charFrob v) :
    ∃ e : M ≃ₗ[A] N, rho.conj e = rho' := by
  sorry

end CyclicBaseChange
