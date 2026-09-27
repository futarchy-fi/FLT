/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.CompletionComparison
public import FLT.GaloisRepresentation.HardlyRamified.Chebotarev.FrobeniusOrder
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Restricting the chosen local Frobenius

The chosen embedding of algebraic closures induces a prime of each finite
global subextension. The local Frobenius congruence restricts to that prime.
-/

@[expose] public section

open NumberField IsDedekindDomain.HeightOneSpectrum
open NumberField.InertiaComparison

-- Use Mathlib's integer-ring action when applying the finite Galois API.
attribute [local instance 200000] RingOfIntegers.instMulSemiringAction
  RingOfIntegers.instAlgebra

namespace GaloisRepresentation.Chebotarev

variable {K : Type*} [Field K] [NumberField K]
variable (v : Prime K) (L : IntermediateField K (AlgebraicClosure K))
  [FiniteDimensional K L] [IsGalois K L]

/-- Restricting the chosen local Frobenius preserves the residue congruence. -/
theorem isArithFrobAt_localRestriction :
    IsArithFrobAt (𝓞 K)
      (localRestriction v L (Field.AbsoluteGaloisGroup.adicArithFrob v))
      (localInducedPrime v L) := by
  have hc : Nat.card ((𝓞 K) ⧸ (localInducedPrime v L).under (𝓞 K)) =
      Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) := by
    rw [← Ideal.over_def (localInducedPrime v L) v.asIdeal]
    exact Nat.card_congr (ResidueFieldEquivCompletionResidueField K v).toEquiv
  intro x
  change localIntegersMap v L (_ - _) ∈ IsLocalRing.maximalIdeal _
  rw [map_sub, map_pow, hc]
  have he := localIntegersMap_equivariant v L
    (Field.AbsoluteGaloisGroup.adicArithFrob v) x
  change localIntegersMap v L
    ((localRestriction v L (Field.AbsoluteGaloisGroup.adicArithFrob v)) • x) = _ at he
  change localIntegersMap v L
    ((localRestriction v L (Field.AbsoluteGaloisGroup.adicArithFrob v)) • x) - _ ∈ _
  rw [he]
  have h := Field.AbsoluteGaloisGroup.isArithFrobAt_adicArithFrob v
    (localIntegersMap v L x)
  rwa [← Ideal.over_def (IsLocalRing.maximalIdeal
    (IntegralClosure (v.adicCompletionIntegers K)
      (AlgebraicClosure (v.adicCompletion K))))
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))] at h

end GaloisRepresentation.Chebotarev
