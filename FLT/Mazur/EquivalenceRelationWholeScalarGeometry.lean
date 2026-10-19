/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationWholeScalarStrata
public import FLT.Mazur.EquivalenceRelationCompleteSpecializations
public import FLT.Mazur.EquivalenceRelationScalarSupportedBaseChange
public import FLT.Mazur.SchemeInvariantClosedScalarImage

/-!
# Exact geometry on the constructed whole-complete scalar locus

Every full character above this locus keeps its own field and unique original
arrows. Arbitrary scalar tests supported in the locus satisfy the exact original
relation equations, including unreduced tests with many scalar support points.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (B : (source p q I o).Opens)
  (hB : ∀ g : Equiv.Perm I, (action e I o g).hom ⁻¹ᵁ B = B)
  [IsAffine B.toScheme]
attribute [local irreducible] source action restrictedAction Complete
local notation "ρ" => restrictedAction (action e I o) B hB
local notation "C" => invariantCoordinates ρ
local notation "u" w => sourceCharacterMap (X := B.toScheme) w ≫ B.ι
variable {R : Type} [CommRing R]
  (σ : R →+* invariantCoordinates (restrictedAction (action e I o) B hB))
local notation "s" => invariantScalarCoordinates ρ σ

/-- Every full character over the constructed scalar locus has complete, uniquely related lifts. -/
theorem exists_wholeScalar_full_character (P : PrimeSpectrum R)
    (hP : P ∈ wholeCompleteScalarLocus e I o B hB σ)
    {F : Type} [Field F] [IsAlgClosed F] (χ : C →+* F)
    (hχ : PrimeSpectrum.comap σ (PrimeSpectrum.comap χ ⊥) = P) :
    ∃ w : Γ(B.toScheme, ⊤) →+* F,
      (∀ r : C, w r.val = χ r) ∧ Complete I o (u w) ∧
      ∀ v : Γ(B.toScheme, ⊤) →+* F,
        (∀ r : C, v r.val = χ r) → Complete I o (u v) ∧
        ∃! a : Spec (.of F) ⟶ D,
          a ≫ p = (u w) ≫ first p q I o ∧ a ≫ q = (u v) ≫ first p q I o :=
  exists_complete_closed_character e I o B hB χ
    (wholeCompleteScalarLocus_full_prime e I o B hB σ P hP _ hχ)

/-- Nonemptiness constructs an exact complete lift over the unchanged scalar residue closure. -/
theorem exists_wholeScalar_residue_character (hs : (s).FiniteType) (P : PrimeSpectrum R)
    (hP : P ∈ wholeCompleteScalarLocus e I o B hB σ) :
    ∃ w : Γ(B.toScheme, ⊤) →+* scalarResidueClosure P,
      w.comp s = algebraMap R (scalarResidueClosure P) ∧ Complete I o (u w) ∧
      sourceCharacterMap w ≫ scalarMorphism s =
        Spec.map (CommRingCat.ofHom (algebraMap R (scalarResidueClosure P))) := by
  obtain ⟨⟨Q, hQ⟩, hc⟩ := (mem_wholeCompleteScalarLocus_iff e I o B hB σ P).mp hP
  obtain ⟨w, hw, hcomplete⟩ := exists_scalar_character_of_closedOrbit ρ
    (B.ι ⁻¹' completePointLocus I o) (completeChart_isClosed I o B)
    (completeChart_stable e I o B hB) σ hs P ⟨Q, hc Q hQ, hQ⟩
  refine ⟨w, hw, (complete_iff_mem_completePointLocus I o (u w)).mpr hcomplete, ?_⟩
  rw [sourceCharacterMap_scalar, hw]

local notation "k" => B.ι ≫ first p q I o
local notation "F" => SchemeRelationRestriction.fst p q k
local notation "H" => SchemeRelationRestriction.snd p q k
local notation "φ" => F ≫ quotientMap ρ ≫ Spec.map (CommRingCat.ofHom σ)

/-- Every scalar test supported in the locus retains exact original equations and nilpotents. -/
theorem wholeScalar_testRelation_equalizes [IsLocallyNoetherian A]
    {T : Scheme} (b : T ⟶ Spec (.of R))
    (hb : ∀ x : T, b x ∈ wholeCompleteScalarLocus e I o B hB σ) (t : C) :
    (scalarTestRelationMap e I o B hB σ b ≫ F).appTop t.val =
      (scalarTestRelationMap e I o B hB σ b ≫ H).appTop t.val := by
  apply completeOrbitSupportedTest_equalizes e I o B hB _ _ t
  rintro _ ⟨x, rfl⟩
  have hc := congrArg (fun a ↦ a x) (pullback.condition (f := φ) (g := b))
  exact wholeCompleteScalarLocus_full_prime e I o B hB σ
    (b (pullback.snd φ b x)) (hb _) _ hc

/-- The finite scalar pieces themselves support exact equations on arbitrary unreduced tests. -/
theorem exists_wholeScalar_equation_strata [IsLocallyNoetherian A]
    [TopologicalSpace.NoetherianSpace B.toScheme] (hfp : σ.FinitePresentation) :
    ∃ pieces : Finset (R × Finset R),
      (∀ P : PrimeSpectrum R, P ∈ wholeCompleteScalarLocus e I o B hB σ ↔
        ∃ a ∈ pieces, a.1 ∉ P.asIdeal ∧ ∀ r ∈ a.2, r ∈ P.asIdeal) ∧
      ∀ a ∈ pieces, ∀ {T : Scheme} (b : T ⟶ Spec (.of R)),
        (∀ x : T, a.1 ∉ (b x).asIdeal ∧ ∀ r ∈ a.2, r ∈ (b x).asIdeal) →
        ∀ t : C, (scalarTestRelationMap e I o B hB σ b ≫ F).appTop t.val =
          (scalarTestRelationMap e I o B hB σ b ≫ H).appTop t.val := by
  obtain ⟨pieces, h⟩ := exists_wholeCompleteScalarLocus_strata e I o B hB σ hfp
  refine ⟨pieces, h, fun a ha T b hb t ↦ ?_⟩
  exact wholeScalar_testRelation_equalizes e I o B hB σ b
    (fun x ↦ (h (b x)).mpr ⟨a, ha, hb x⟩) t

end FLT.Mazur.EquivalenceRelationNormalizedFrames
