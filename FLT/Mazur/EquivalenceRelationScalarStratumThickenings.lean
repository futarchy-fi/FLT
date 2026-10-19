/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationWholeScalarGeometry
public import FLT.Mazur.ScalarStratumThickenings
public import FLT.Mazur.ScalarStrataBoundaryRefinement

/-!
# Constructed infinitesimal scalar stratum tests satisfy original equations

For each finite scalar piece of the whole-complete locus, build every positive
power thickening and invert its denominator. These actual tests cover the same
piece at every order and equalize the full unchanged original relation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient ScalarConstructibleStrata
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (B : (source p q I o).Opens)
  (hB : ∀ g : Equiv.Perm I, (action e I o g).hom ⁻¹ᵁ B = B)
  [IsAffine B.toScheme]
attribute [local irreducible] source action restrictedAction
local notation "ρ" => restrictedAction (action e I o) B hB
local notation "C" => invariantCoordinates ρ
local notation "k" => B.ι ≫ first p q I o
local notation "F" => SchemeRelationRestriction.fst p q k
local notation "H" => SchemeRelationRestriction.snd p q k
variable {R : Type} [CommRing R]
  (σ : R →+* invariantCoordinates (restrictedAction (action e I o) B hB))
local notation "test" a:max order:max => Spec.map (CommRingCat.ofHom (stratumThickeningMap a order))

/-- Every constructed infinitesimal order of a whole-complete scalar piece has exact equations. -/
theorem scalarStratumThickening_equalizes [IsLocallyNoetherian A]
    (a : R × Finset R)
    (ha : ∀ P : PrimeSpectrum R,
      a.1 ∉ P.asIdeal → (∀ r ∈ a.2, r ∈ P.asIdeal) →
        P ∈ wholeCompleteScalarLocus e I o B hB σ)
    (order : ℕ) (t : C) :
    (scalarTestRelationMap e I o B hB σ (test a order) ≫ F).appTop t.val =
      (scalarTestRelationMap e I o B hB σ (test a order) ≫ H).appTop t.val := by
  apply wholeScalar_testRelation_equalizes e I o B hB σ (test a order) _ t
  intro x
  exact ha _ (stratumThickening_support a order x).1
    (stratumThickening_support a order x).2

/-- Construct a finite scalar cover whose actual thickened tests work at every order. -/
theorem exists_scalarStratumThickening_equation_cover [IsLocallyNoetherian A]
    [TopologicalSpace.NoetherianSpace B.toScheme] (hfp : σ.FinitePresentation) :
    ∃ pieces : Finset (R × Finset R),
      (∀ P : PrimeSpectrum R, P ∈ wholeCompleteScalarLocus e I o B hB σ ↔
        ∃ a ∈ pieces, a.1 ∉ P.asIdeal ∧ ∀ r ∈ a.2, r ∈ P.asIdeal) ∧
      ∀ a ∈ pieces, ∀ (order : ℕ) (t : C),
        (scalarTestRelationMap e I o B hB σ (test a order) ≫ F).appTop t.val =
          (scalarTestRelationMap e I o B hB σ (test a order) ≫ H).appTop t.val := by
  obtain ⟨pieces, h⟩ := exists_wholeCompleteScalarLocus_strata e I o B hB σ hfp
  refine ⟨pieces, h, fun a ha order t ↦ ?_⟩
  exact scalarStratumThickening_equalizes e I o B hB σ a
    (fun P ht he ↦ (h P).mpr ⟨a, ha, ht, he⟩) order t

/-- The remaining scalar boundary has actual equation tests at every infinitesimal order. -/
theorem exists_boundary_scalarStratumThickening_cover [IsLocallyNoetherian A]
    [TopologicalSpace.NoetherianSpace B.toScheme] (hfp : σ.FinitePresentation)
    (cuts : Finset R) :
    ∃ pieces : Finset (R × Finset R),
      (∀ P : PrimeSpectrum R,
        (P ∈ wholeCompleteScalarLocus e I o B hB σ ∧ ∀ r ∈ cuts, r ∈ P.asIdeal) ↔
          ∃ a ∈ pieces, a.1 ∉ P.asIdeal ∧ ∀ r ∈ a.2, r ∈ P.asIdeal) ∧
      ∀ a ∈ pieces, ∀ (order : ℕ) (t : C),
        (scalarTestRelationMap e I o B hB σ (test a order) ≫ F).appTop t.val =
          (scalarTestRelationMap e I o B hB σ (test a order) ≫ H).appTop t.val := by
  obtain ⟨pieces, h⟩ := exists_wholeCompleteScalarLocus_strata e I o B hB σ hfp
  refine ⟨boundaryPieces pieces cuts, ?_, ?_⟩
  · intro P
    rw [boundaryPieces_iff, h P]
  · intro a ha order t
    apply scalarStratumThickening_equalizes e I o B hB σ a _ order t
    intro P ht he
    exact (h P).mpr ((boundaryPieces_iff pieces cuts P).mp ⟨a, ha, ht, he⟩).1

end FLT.Mazur.EquivalenceRelationNormalizedFrames
