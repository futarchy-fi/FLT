/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationInvariantCharacterArrows
public import FLT.Mazur.SchemeFiniteGroupCharacterLifts

/-!
# Geometric quotient fibers and the full original relation

Over a complete first frame, equality in the actual affine invariant quotient
is precisely the full original relation, including the field-valued endpoint
maps. Every algebraically closed quotient character also has a constructed
representative and a unique original arrow to every other lift.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source action restrictedAction
variable {D A : Scheme} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (U : (source p q I o).Opens)
  (hU : ∀ g : Equiv.Perm I, (action e I o g).hom ⁻¹ᵁ U = U)
  [IsAffine U.toScheme] {K : Type} [Field K]
  (v w : Γ(U.toScheme, ⊤) →+* K)
local notation "ρ" => restrictedAction (action e I o) U hU
local notation "u" z => sourceCharacterMap (X := U.toScheme) z ≫ U.ι


/-- A full original arrow out of a complete frame identifies all frame invariants. -/
theorem invariant_characters_of_complete_original_arrow
    (hv : Complete I o (u v)) (a : Spec (.of K) ⟶ D)
    (ha : a ≫ p = (u v) ≫ first p q I o)
    (hb : a ≫ q = (u w) ≫ first p q I o) :
    ∀ t : invariantCoordinates (restrictedAction (action e I o) U hU),
      v t.val = w t.val := by
  obtain ⟨g, hg, _⟩ := complete_original_arrow_unique_permutation
    e I o (u v) (u w) a ha hb hv
  have he : sourceCharacterMap v ≫ (ρ g).hom = sourceCharacterMap w := by
    apply (cancel_mono U.ι).mp
    simpa only [Category.assoc, restrictedAction_hom_ι] using hg
  apply (sourceCharacterMap_quotient_eq_iff ρ v w).mp
  exact (sourceCharacterMap_quotient_eq_iff_orbit ρ v w).mpr ⟨g, he⟩

/-- The quotient kernel at a complete frame is exactly the full original geometric relation. -/
theorem complete_quotient_fiber_iff_original_arrow (hv : Complete I o (u v)) :
    sourceCharacterMap v ≫ quotientMap (restrictedAction (action e I o) U hU) =
      sourceCharacterMap w ≫ quotientMap (restrictedAction (action e I o) U hU) ↔
    ∃ a : Spec (.of K) ⟶ D,
      a ≫ p = (u v) ≫ first p q I o ∧ a ≫ q = (u w) ≫ first p q I o := by
  constructor
  · intro h
    exact (invariant_character_original_arrow e I o U hU v w
      ((sourceCharacterMap_quotient_eq_iff ρ v w).mp h)).exists
  · rintro ⟨a, ha, hb⟩
    exact (sourceCharacterMap_quotient_eq_iff ρ v w).mpr
      (invariant_characters_of_complete_original_arrow e I o U hU v w hv a ha hb)

variable [IsAlgClosed K]

omit [Etale p] in
/-- Construct a representative and unique original arrows throughout its quotient fiber. -/
theorem exists_invariant_character_original_orbit
    (χ : invariantCoordinates (restrictedAction (action e I o) U hU) →+* K) :
    ∃ v : Γ(U.toScheme, ⊤) →+* K,
      (∀ t : invariantCoordinates (restrictedAction (action e I o) U hU), v t.val = χ t) ∧
      ∀ w : Γ(U.toScheme, ⊤) →+* K,
        (∀ t : invariantCoordinates (restrictedAction (action e I o) U hU), w t.val = χ t) →
        ∃! a : Spec (.of K) ⟶ D,
          a ≫ p = (u v) ≫ first p q I o ∧ a ≫ q = (u w) ≫ first p q I o := by
  obtain ⟨v, hv⟩ := exists_sourceCharacter_lift ρ χ
  exact ⟨v, hv, fun w hw ↦ invariant_character_original_arrow e I o U hU v w
    (fun t ↦ (hv t).trans (hw t).symm)⟩

end FLT.Mazur.EquivalenceRelationNormalizedFrames
