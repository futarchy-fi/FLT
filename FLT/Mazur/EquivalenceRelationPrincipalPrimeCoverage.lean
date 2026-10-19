/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationPrincipalCompleteCharacters
public import FLT.Mazur.ScalarResidueClosureGeometry

/-!
# Every prime in a constructed full-invariant neighborhood has complete geometry

The invariant denominator constructed from one interior complete point reaches
every prime of its principal quotient open. Each lift is over that prime's
canonical residue closure and retains its exact full character. No minimality
or source scalar flatness is required; the ring here is the full chart invariant
ring, not a replacement for a separately prescribed original scalar ring.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (B : (source p q I o).Opens)
  (hB : ∀ g : Equiv.Perm I, (action e I o g).hom ⁻¹ᵁ B = B)
  [IsAffine B.toScheme]
local notation "ρ" => restrictedAction (action e I o) B hB
local notation "C" => invariantCoordinates ρ
local notation "K" Q => scalarResidueClosure Q
local notation "u" w => sourceCharacterMap (X := B.toScheme) w ≫ B.ι
attribute [local irreducible] source action restrictedAction completeInterior Complete
  scalarResidueClosureField scalarResidueClosureAlgebra

/-- The constructed principal quotient neighborhood covers all its primes, not just minimal ones. -/
theorem exists_complete_principal_prime_neighborhood (x : B.toScheme)
    (hx : B.ι x ∈ completeInterior (p := p) (q := q) I o) :
    ∃ t : C, x ∈ B.toScheme.basicOpen t.val ∧
      ∀ Q : PrimeSpectrum C, t ∉ Q.asIdeal →
      ∃ w : Γ(B.toScheme, ⊤) →+* K Q,
        (∀ r : C, w r.val = algebraMap C (K Q) r) ∧
        (u w) default ∈ completeInterior (p := p) (q := q) I o ∧
        Complete I o (u w) ∧
        sourceCharacterMap w ≫ quotientMap ρ =
          Spec.map (CommRingCat.ofHom (algebraMap C (K Q))) ∧
        quotientMap ρ (sourceCharacterMap w default) = Q := by
  obtain ⟨t, ht, hC⟩ := exists_complete_principal_character_neighborhood e I o B hB x hx
  refine ⟨t, ht, fun Q hQ ↦ ?_⟩
  have hn : algebraMap C (K Q) t ≠ 0 := by
    change t ∉ (PrimeSpectrum.comap (algebraMap C (K Q)) ⊥).asIdeal
    rwa [scalarResidueClosure_center]
  obtain ⟨w, hw, hi, hc, _⟩ := hC (algebraMap C (K Q)) hn
  have he : sourceCharacterMap w ≫ quotientMap ρ =
      Spec.map (CommRingCat.ofHom (algebraMap C (K Q))) := by
    rw [sourceCharacterMap_quotient]
    apply congrArg Spec.map
    ext r
    exact hw r
  refine ⟨w, hw, hi, hc, he, ?_⟩
  rw [← Scheme.Hom.comp_apply, he]
  exact scalarResidueClosure_center Q

end FLT.Mazur.EquivalenceRelationNormalizedFrames
