/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteScalarFiber
public import FLT.Mazur.EquivalenceRelationInvariantCharacterArrows
public import FLT.Mazur.SchemeFiniteGroupCharacterLifts
public import FLT.Mazur.ScalarResidueClosureGeometry

/-!
# Specializations of complete full invariant primes

The complete orbit locus is closed. Every specialization of a complete
invariant prime therefore has complete representatives over every algebraically
closed field realizing that full character, even outside the complete interior.
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
attribute [local irreducible] source action restrictedAction Complete
  scalarResidueClosureField scalarResidueClosureAlgebra

/-- Completeness extends to every specialization in the full invariant spectrum. -/
theorem complete_orbit_specialization (x : B.toScheme)
    (hx : B.ι x ∈ completePointLocus (p := p) (q := q) I o)
    (Q : PrimeSpectrum C) (hQ : (quotientMap ρ x).asIdeal ≤ Q.asIdeal) :
    Q ∈ completeAffineOrbitImage e I o B hB := by
  have hi : quotientMap ρ x ∈ completeAffineOrbitImage e I o B hB := by
    exact ⟨x, hx, rfl⟩
  change quotientMap ρ x ∈ (completeAffineOrbitImage e I o B hB : Set (quotient ρ)) at hi
  change Q ∈ (completeAffineOrbitImage e I o B hB : Set (quotient ρ))
  rw [← completeAffineOrbitIdeal_zeroLocus] at hi ⊢
  exact fun r hr ↦ hQ (hi hr)

/-- Every full character centered on the complete closed locus has complete original lifts. -/
theorem exists_complete_closed_character {F : Type} [Field F] [IsAlgClosed F]
    (χ : C →+* F)
    (hχ : PrimeSpectrum.comap χ ⊥ ∈ completeAffineOrbitImage e I o B hB) :
    ∃ w : Γ(B.toScheme, ⊤) →+* F,
      (∀ r : C, w r.val = χ r) ∧ Complete I o (u w) ∧
      ∀ v : Γ(B.toScheme, ⊤) →+* F,
        (∀ r : C, v r.val = χ r) → Complete I o (u v) ∧
        ∃! a : Spec (.of F) ⟶ D,
          a ≫ p = (u w) ≫ first p q I o ∧ a ≫ q = (u v) ≫ first p q I o := by
  obtain ⟨w, hw⟩ := exists_sourceCharacter_lift ρ χ
  have hc (v : Γ(B.toScheme, ⊤) →+* F) (hv : ∀ r : C, v r.val = χ r) :
      Complete I o (u v) := by
    have he : sourceCharacterMap v ≫ quotientMap ρ = Spec.map (CommRingCat.ofHom χ) := by
      rw [sourceCharacterMap_quotient]
      apply congrArg Spec.map
      ext r
      exact hv r
    apply (complete_iff_mem_completePointLocus I o (u v)).mpr
    change sourceCharacterMap v default ∈ B.ι ⁻¹' completePointLocus I o
    rw [← completeAffineOrbitImage_preimage e I o B hB]
    change (sourceCharacterMap v ≫ quotientMap ρ) default ∈
      (completeAffineOrbitImage e I o B hB : Set (quotient ρ))
    rw [he]
    exact hχ
  refine ⟨w, hw, hc w hw, fun v hv ↦ ⟨hc v hv, ?_⟩⟩
  exact invariant_character_original_arrow e I o B hB w v
    (fun r ↦ (hw r).trans (hv r).symm)

/-- Nonminimal specializations have exact complete lifts over their own residue closures. -/
theorem exists_complete_specialization_character (x : B.toScheme)
    (hx : B.ι x ∈ completePointLocus (p := p) (q := q) I o)
    (Q : PrimeSpectrum C) (hQ : (quotientMap ρ x).asIdeal ≤ Q.asIdeal) :
    ∃ w : Γ(B.toScheme, ⊤) →+* K Q,
      (∀ r : C, w r.val = algebraMap C (K Q) r) ∧ Complete I o (u w) := by
  have hm := complete_orbit_specialization e I o B hB x hx Q hQ
  rw [← scalarResidueClosure_center Q] at hm
  obtain ⟨w, hw, hc, _⟩ := exists_complete_closed_character e I o B hB
    (algebraMap C (K Q)) hm
  exact ⟨w, hw, hc⟩

end FLT.Mazur.EquivalenceRelationNormalizedFrames
