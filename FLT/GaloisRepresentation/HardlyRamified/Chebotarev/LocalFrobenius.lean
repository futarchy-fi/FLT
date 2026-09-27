/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.CompletionComparison
public import FLT.GaloisRepresentation.HardlyRamified.Chebotarev.FrobeniusOrder
public import FLT.Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
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

namespace GaloisRepresentation.B5Inputs

-- Match the completion structures in B5Inputs and GaloisRep.toLocal.
attribute [local instance 2000] adicCompletion.instField instAlgebraAdicCompletion

/-- The exact chosen local Frobenius used by the B5 trace criterion. -/
noncomputable abbrev QFrob (q : ℕ) (hq : q.Prime) : Field.absoluteGaloisGroup ℚ :=
  Field.absoluteGaloisGroup.map
    (algebraMap ℚ (hq.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ))
    (Field.AbsoluteGaloisGroup.adicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat)

end GaloisRepresentation.B5Inputs

namespace GaloisRepresentation.Chebotarev

open GaloisRepresentation.B5Inputs

/-- An automorphism is Frobenius at some prime above the given base prime. -/
def HasFrob (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] (v : Prime K) (σ : Gal(L/K)) : Prop :=
  ∃ w : Prime L, w.asIdeal.under (𝓞 K) = v.asIdeal ∧ IsArithFrobAt (𝓞 K) σ w.asIdeal

open scoped Pointwise in
/-- All Frobenius choices above an unramified prime are conjugate. -/
theorem isConj_frob_of_hasFrob (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (v : Prime K) (hu : Unram K L v) (σ : Gal(L/K)) (hσ : HasFrob K L v σ) :
    IsConj σ (frob K L v) := by
  obtain ⟨w, hw, hσ⟩ := hσ
  let : w.asIdeal.LiesOver v.asIdeal := ⟨hw.symm⟩
  let : (primeAbove K L v).asIdeal.LiesOver v.asIdeal :=
    ⟨(primeAbove_under K L v).symm⟩
  let : Algebra.IsUnramifiedAt (𝓞 K) (primeAbove K L v).asIdeal :=
    hu _ inferInstance inferInstance
  obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup
    v.asIdeal w.asIdeal (primeAbove K L v).asIdeal Gal(L/K)
  have hc := hσ.conj τ
  rw [hτ] at hc
  have hi := hc.mul_inv_mem_inertia (isArithFrobAt_frob K L v)
  rw [inertia_eq_bot_of_isUnramifiedAt K L (primeAbove K L v),
    Subgroup.mem_bot] at hi
  exact isConj_iff.mpr ⟨τ, mul_inv_eq_one.mp hi⟩

variable (L : IntermediateField ℚ (AlgebraicClosure ℚ))
  [FiniteDimensional ℚ L]

/-- The prime induced by B5's chosen local embedding, as a nonzero prime. -/
noncomputable def qFrobPrime (q : ℕ) (hq : q.Prime) : Prime L :=
  ⟨localInducedPrime hq.toHeightOneSpectrumRingOfIntegersRat L,
    inferInstance, localInducedPrime_ne_bot _ _⟩

/-- The prime selected by the chosen embedding contracts to the original rational prime. -/
theorem qFrobPrime_under (q : ℕ) (hq : q.Prime) :
    (qFrobPrime L q hq).asIdeal.under (𝓞 ℚ) =
      hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal :=
  (Ideal.over_def (localInducedPrime hq.toHeightOneSpectrumRingOfIntegersRat L)
    hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal).symm

variable [IsGalois ℚ L]

/-- The restriction of B5's Frobenius is Frobenius at its induced prime.
This congruence holds even at ramified primes. -/
theorem isArithFrobAt_restrict_QFrob (q : ℕ) (hq : q.Prime) :
    IsArithFrobAt (𝓞 ℚ) (AlgEquiv.restrictNormalHom L (QFrob q hq))
      (qFrobPrime L q hq).asIdeal := by
  exact isArithFrobAt_localRestriction hq.toHeightOneSpectrumRingOfIntegersRat L

/-- B5's chosen Frobenius restricts to a Frobenius above the rational prime (G4).
The unramifiedness hypothesis is retained to match the plan's interface;
only the subsequent conjugacy theorem needs it. -/
@[nolint unusedArguments]
theorem hasFrob_restrict_QFrob (q : ℕ) (hq : q.Prime)
    (_hu : Unram ℚ L hq.toHeightOneSpectrumRingOfIntegersRat) :
    HasFrob ℚ L hq.toHeightOneSpectrumRingOfIntegersRat
      (AlgEquiv.restrictNormalHom L (QFrob q hq)) :=
  ⟨qFrobPrime L q hq, qFrobPrime_under L q hq, isArithFrobAt_restrict_QFrob L q hq⟩

/-- B5's chosen local Frobenius and the independently chosen finite Frobenius
are conjugate at every unramified rational prime (G4). -/
theorem isConj_restrict_QFrob_frob (q : ℕ) (hq : q.Prime)
    (hu : Unram ℚ L hq.toHeightOneSpectrumRingOfIntegersRat) :
    IsConj (AlgEquiv.restrictNormalHom L (QFrob q hq))
      (frob ℚ L hq.toHeightOneSpectrumRingOfIntegersRat) :=
  isConj_frob_of_hasFrob ℚ L hq.toHeightOneSpectrumRingOfIntegersRat hu _
    (hasFrob_restrict_QFrob L q hq hu)

end GaloisRepresentation.Chebotarev
