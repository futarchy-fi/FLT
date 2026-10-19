/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFiniteGroupCharacterOrbits
public import FLT.Mazur.EquivalenceRelationGeometricTestExtensions

/-!
# Original relation arrows constructed from full invariant characters

Agreement on all invariants of a stable affine frame chart constructs an
actual original relation arrow over the same field. Neither endpoint is
assumed complete for this construction. A complete first frame then forces
the second frame to be complete, with exactly the original label set.
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


omit [Etale p] in
/-- Full invariant character equality constructs the unique normalized permutation. -/
theorem invariant_character_unique_permutation
    (h : ∀ t : invariantCoordinates (restrictedAction (action e I o) U hU),
      v t.val = w t.val) :
    ∃! g : Equiv.Perm I, (u v) ≫ (action e I o g).hom = u w := by
  obtain ⟨g, hg⟩ := sourceCharacterMap_orbit_of_invariants ρ v w h
  have he : (u v) ≫ (action e I o g).hom = u w := by
    have hi := congrArg (fun a ↦ a ≫ U.ι) hg
    simpa only [Category.assoc, restrictedAction_hom_ι] using hi
  exact ⟨g, he, fun g' hg' ↦ action_unique e I o (u v) (u w) g' g hg' he⟩

omit [Etale p] in
/-- Construct the actual original arrow, retaining both specified field-valued endpoints. -/
theorem invariant_character_original_arrow
    (h : ∀ t : invariantCoordinates (restrictedAction (action e I o) U hU),
      v t.val = w t.val) :
    ∃! a : Spec (.of K) ⟶ D,
      a ≫ p = (u v) ≫ first p q I o ∧ a ≫ q = (u w) ≫ first p q I o := by
  obtain ⟨g, hg, _⟩ := invariant_character_unique_permutation e I o U hU v w h
  let a := (u v) ≫ actionArrow (p := p) (q := q) I o g
  have ha : a ≫ p = (u v) ≫ first p q I o := by
    change ((u v) ≫ actionArrow I o g) ≫ p = _
    rw [Category.assoc, actionArrow_first]
  have hb : a ≫ q = (u w) ≫ first p q I o := by
    change ((u v) ≫ actionArrow I o g) ≫ q = _
    rw [Category.assoc, actionArrow_second e, ← Category.assoc, hg]
  refine ⟨a, ⟨ha, hb⟩, fun a' ha' ↦ ?_⟩
  exact e.right_cancellation a' a (ha'.1.trans ha.symm) (ha'.2.trans hb.symm)

/-- A complete representative supplies completeness through the constructed original arrow. -/
theorem complete_of_invariant_character
    (h : ∀ t : invariantCoordinates (restrictedAction (action e I o) U hU),
      v t.val = w t.val) (hv : Complete I o (u v)) :
    Complete I o (u w) := by
  obtain ⟨a, ⟨ha, hb⟩, _⟩ := invariant_character_original_arrow e I o U hU v w h
  exact complete_of_original_arrow e I o (u v) (u w) a ha hb hv

end FLT.Mazur.EquivalenceRelationNormalizedFrames
