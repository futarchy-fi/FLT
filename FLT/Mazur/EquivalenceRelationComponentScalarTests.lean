/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteComponents
public import FLT.Mazur.EquivalenceRelationScalarSupportedBaseChange

/-!
# Exact original relation equations from quotient component anchors

Anchors on every quotient component fill the complete orbit locus. The actual
original relation then equalizes invariant coordinates on every test scheme,
including unreduced scalar tests. This needs neither scalar flatness nor scalar
finite type; the component anchors remain geometric inputs on the fixed chart.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient ScalarTestLocalization
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source action restrictedAction
variable {D A : Scheme} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (U : (source p q I o).Opens)
  (hU : ∀ g : Equiv.Perm I, (action e I o g).hom ⁻¹ᵁ U = U)
  [IsAffine U.toScheme]
local notation "k" => U.ι ≫ first p q I o
local notation "F" => SchemeRelationRestriction.fst p q k
local notation "H" => SchemeRelationRestriction.snd p q k
local notation "Rel" => SchemeRelationRestriction.doubleDomain p q k
local notation "ρ" => restrictedAction (action e I o) U hU
local notation "J" => completeAffineOrbitIdeal e I o U hU
/-- Every full invariant prime is complete once every component has an interior anchor. -/
theorem complete_orbit_mem_of_component_anchors
    (hanchors : ∀ Z ∈ irreducibleComponents (quotient ρ),
      ∃ x : U.toScheme, U.ι x ∈ completeInterior (p := p) (q := q) I o ∧
        quotientMap ρ x ∈ Z)
    (Q : quotient ρ) :
    Q ∈ completeAffineOrbitImage e I o U hU := by
  obtain ⟨y, hy⟩ := (quotientMap ρ).surjective Q
  exact ⟨y, complete_fixed_chart_of_component_anchors e I o U hU hanchors y, hy⟩

/-- Original arrows on any test scheme equalize full invariant coordinates. -/
theorem originalRelationTest_equalizes_of_component_anchors [IsLocallyNoetherian A]
    (hanchors : ∀ Z ∈ irreducibleComponents (quotient ρ),
      ∃ x : U.toScheme, U.ι x ∈ completeInterior (p := p) (q := q) I o ∧
        quotientMap ρ x ∈ Z)
    {T : Scheme} (g : T ⟶ Rel) (t : invariantCoordinates ρ) :
    (g ≫ F).appTop t.val = (g ≫ H).appTop t.val := by
  apply completeOrbitSupportedTest_equalizes e I o U hU g _ t
  intro Q _
  exact complete_orbit_mem_of_component_anchors e I o U hU hanchors Q

variable {R : Type} [CommRing R]
  (s : R →+* invariantCoordinates (restrictedAction (action e I o) U hU))

/-- Arbitrary original scalar tests retain their nilpotents and satisfy the exact equations. -/
theorem scalarTestRelation_equalizes_of_component_anchors [IsLocallyNoetherian A]
    (hanchors : ∀ Z ∈ irreducibleComponents (quotient ρ),
      ∃ x : U.toScheme, U.ι x ∈ completeInterior (p := p) (q := q) I o ∧
        quotientMap ρ x ∈ Z)
    {T : Scheme} (b : T ⟶ Spec (.of R)) (t : invariantCoordinates ρ) :
    (scalarTestRelationMap e I o U hU s b ≫ F).appTop t.val =
      (scalarTestRelationMap e I o U hU s b ≫ H).appTop t.val :=
  originalRelationTest_equalizes_of_component_anchors e I o U hU hanchors _ t

end FLT.Mazur.EquivalenceRelationNormalizedFrames
