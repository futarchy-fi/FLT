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
characteristic polynomials, and semisimplicity explicitly.

The library does not yet contain the required Chebotarev density or Brauer--Nesbitt theorems, so
the comparison theorem below takes their precise outputs as explicit hypotheses.  Keeping these
two inputs separate records exactly which mathematical infrastructure remains to be supplied.
-/

@[expose] public section

open NumberField

namespace CyclicBaseChange

universe uK uA uM uN

local notation "Ω" K => IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)

/-- Two semisimple continuous Galois representations with matching Frobenius characteristic
polynomials away from a finite set are isomorphic, assuming the missing Chebotarev and
Brauer--Nesbitt comparison steps.

`hchebotarev` upgrades the local Frobenius data to equality of characteristic polynomials on the
whole Galois group.  `hbrauerNesbitt` says that this equality determines a semisimple
representation.  Both are explicit because neither theorem is currently available in Mathlib or
FLT. -/
theorem exists_conjugating_equiv_of_charFrob_eq_outside
    {K : Type uK} [Field K] [NumberField K]
    {A : Type uA} [Field A] [TopologicalSpace A]
    {M : Type uM} [AddCommGroup M] [Module A M] [Module.Free A M] [Module.Finite A M]
    {N : Type uN} [AddCommGroup N] [Module A N] [Module.Free A N] [Module.Finite A N]
    (rho : GaloisRep K A M) (rho' : GaloisRep K A N) (exceptional : Finset (Ω K))
    (hsemisimple : rho.toRepresentation.IsSemisimpleRepresentation)
    (hsemisimple' : rho'.toRepresentation.IsSemisimpleRepresentation)
    (hunramified : ∀ v, v ∉ exceptional →
      GaloisRep.IsUnramifiedAt rho v ∧ GaloisRep.IsUnramifiedAt rho' v)
    (hcharpoly : ∀ v, v ∉ exceptional → rho.charFrob v = rho'.charFrob v)
    (hchebotarev :
      (∀ v, v ∉ exceptional → GaloisRep.IsUnramifiedAt rho v ∧
        GaloisRep.IsUnramifiedAt rho' v ∧ rho.charFrob v = rho'.charFrob v) →
      ∀ σ, (rho σ).charpoly = (rho' σ).charpoly)
    (hbrauerNesbitt :
      rho.toRepresentation.IsSemisimpleRepresentation →
      rho'.toRepresentation.IsSemisimpleRepresentation →
      (∀ σ, (rho σ).charpoly = (rho' σ).charpoly) →
      Nonempty (rho.toRepresentation.Equiv rho'.toRepresentation)) :
    ∃ e : M ≃ₗ[A] N, rho.conj e = rho' := by
  have hlocal : ∀ v, v ∉ exceptional → GaloisRep.IsUnramifiedAt rho v ∧
      GaloisRep.IsUnramifiedAt rho' v ∧ rho.charFrob v = rho'.charFrob v := by
    intro v hv
    exact ⟨(hunramified v hv).1, (hunramified v hv).2, hcharpoly v hv⟩
  obtain ⟨e⟩ := hbrauerNesbitt hsemisimple hsemisimple' (hchebotarev hlocal)
  refine ⟨e.toLinearEquiv, ?_⟩
  ext σ x
  exact DFunLike.congr_fun (Representation.Equiv.conj_apply_self σ e) x

end CyclicBaseChange
