/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteSpecializations
public import FLT.Mazur.ScalarClosedImageStrata

/-!
# Scalar strata of all complete points on a fixed frame chart

Use the equations of the actual closed complete orbit locus. No interior
anchor is needed: the finite strata include all complete boundary points.
They cover exactly the scalar primes with a complete lift on this fixed chart.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient SchemeScalarPrincipalNeighborhood
open ScalarClosedImageCoverage
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (B : (source p q I o).Opens)
  (hB : ∀ g : Equiv.Perm I, (action e I o g).hom ⁻¹ᵁ B = B)
  [IsAffine B.toScheme]
local notation "ρ" => restrictedAction (action e I o) B hB
local notation "C" => invariantCoordinates ρ
local notation "i" => invariantScalarCoordinates ρ (RingHom.id C)
local notation "J" => Ideal.map i (completeAffineOrbitIdeal e I o B hB)
local notation "u" w => sourceCharacterMap (X := B.toScheme) w ≫ B.ι
attribute [local irreducible] source action restrictedAction Complete
attribute [local semireducible] scalarResidueClosure

/-- Closed orbit equations in the unchanged source ring detect every complete character. -/
theorem complete_character_iff_closed_equations {F : Type} [Field F]
    (w : Γ(B.toScheme, ⊤) →+* F) :
    Complete I o (u w) ↔ ∀ b ∈ J, w b = 0 := by
  rw [complete_iff_mem_completePointLocus]
  change sourceCharacterMap w default ∈ B.ι ⁻¹' completePointLocus I o ↔ _
  rw [← completeAffineOrbitImage_preimage e I o B hB]
  change (sourceCharacterMap w ≫ quotientMap ρ) default ∈
    (completeAffineOrbitImage e I o B hB : Set (quotient ρ)) ↔ _
  rw [sourceCharacterMap_quotient, ← completeAffineOrbitIdeal_zeroLocus]
  change _ ↔ J ≤ RingHom.ker w
  rw [Ideal.map_le_iff_le_comap]
  rfl

variable {R : Type} [CommRing R]
  (σ : R →+* invariantCoordinates (restrictedAction (action e I o) B hB))
local notation "s" => invariantScalarCoordinates ρ σ
local notation "K" P => scalarResidueClosure P

/-- Finite equations cover exactly every scalar prime having an actual complete fixed-chart lift. -/
theorem exists_complete_scalar_image_strata
    (hfp : ((Ideal.Quotient.mk J).comp s).FinitePresentation) :
    ∃ pieces : Finset (R × Finset R), ∀ P : PrimeSpectrum R,
      (∃ a ∈ pieces, a.1 ∉ P.asIdeal ∧ ∀ r ∈ a.2, r ∈ P.asIdeal) ↔
      ∃ w : Γ(B.toScheme, ⊤) →+* K P,
        w.comp s = algebraMap R (K P) ∧ Complete I o (u w) := by
  obtain ⟨pieces, h⟩ := exists_closed_scalar_image_strata s J hfp
  refine ⟨pieces, fun P ↦ ?_⟩
  rw [h P]
  apply exists_congr
  intro w
  exact and_congr_right fun _ ↦ (complete_character_iff_closed_equations e I o B hB w).symm

/-- Finite type over a Noetherian scalar ring constructs all complete-image strata. -/
theorem exists_complete_scalar_image_strata_of_finiteType [IsNoetherianRing R]
    (hs : (s).FiniteType) :
    ∃ pieces : Finset (R × Finset R), ∀ P : PrimeSpectrum R,
      (∃ a ∈ pieces, a.1 ∉ P.asIdeal ∧ ∀ r ∈ a.2, r ∈ P.asIdeal) ↔
      ∃ w : Γ(B.toScheme, ⊤) →+* K P,
        w.comp s = algebraMap R (K P) ∧ Complete I o (u w) := by
  let g := (Ideal.Quotient.mk J).comp s
  have ht : g.FiniteType :=
    (RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective).comp hs
  have hp : g.FinitePresentation := by
    let _ := g.toAlgebra
    exact Algebra.FinitePresentation.of_finiteType.mp ht
  exact exists_complete_scalar_image_strata e I o B hB σ hp

end FLT.Mazur.EquivalenceRelationNormalizedFrames
