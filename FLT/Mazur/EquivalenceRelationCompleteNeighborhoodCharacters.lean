/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationGenericCompleteNeighborhood
public import FLT.Mazur.EquivalenceRelationCompleteCharacterLifts

/-!
# Full invariant characters on constructed complete generic neighborhoods

The actual generic complete neighborhood has complete representatives for
EVERY character of its full invariant ring, over every algebraically closed
field. No vanishing ideal or scalar-character containment is an input.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)

/-- On an actual complete open, every full invariant character has a complete source lift. -/
theorem completeOpen_character_lift (U : (source p q I o).Opens)
    (hU : ∀ g : Equiv.Perm I, (action e I o g).hom ⁻¹ᵁ U = U)
    [IsAffine U.toScheme]
    (hC : (U : Set _) ⊆ completePointLocus (p := p) (q := q) I o)
    {K : Type} [Field K] [IsAlgClosed K]
    (χ : invariantCoordinates (restrictedAction (action e I o) U hU) →+* K) :
    ∃ w : Γ(U.toScheme, ⊤) →+* K,
      (∀ t : invariantCoordinates (restrictedAction (action e I o) U hU), w t.val = χ t) ∧
      Complete I o (sourceCharacterMap w ≫ U.ι) := by
  obtain ⟨w, hw⟩ := exists_sourceCharacter_lift (restrictedAction (action e I o) U hU) χ
  refine ⟨w, hw, (complete_iff_mem_completePointLocus I o _).mpr ?_⟩
  exact hC (sourceCharacterMap w default).property

variable [QuasiCompact p] [IsIntegral A]

/-- Generic complete frames construct an affine chart with complete lifts of all full characters. -/
theorem exists_generic_complete_character_chart {Y : Scheme} [IsAffine Y]
    (j : source p q I o ⟶ Y) [IsOpenImmersion j]
    (x : source p q I o) (hx : first p q I o x = genericPoint A)
    (hc : x ∈ completePointLocus (p := p) (q := q) I o)
    (W : (source p q I o).Opens) (hW : frameOrbit e I o x ⊆ W) :
    ∃ (U : (source p q I o).Opens)
      (hU : ∀ g : Equiv.Perm I, (action e I o g).hom ⁻¹ᵁ U = U)
      (hA : IsAffineOpen U), frameOrbit e I o x ⊆ U ∧ U ≤ W ∧
      let _ : IsAffine U.toScheme := hA
      ∀ (K : Type) [Field K] [IsAlgClosed K]
        (χ : invariantCoordinates (restrictedAction (action e I o) U hU) →+* K),
        ∃ w : Γ(U.toScheme, ⊤) →+* K,
          (∀ t : invariantCoordinates (restrictedAction (action e I o) U hU),
            w t.val = χ t) ∧ Complete I o (sourceCharacterMap w ≫ U.ι) := by
  obtain ⟨U, hA, hO, hUW, hC, hU⟩ := exists_generic_complete_affine e I o j x hx hc W hW
  refine ⟨U, hU, hA, hO, hUW, ?_⟩
  dsimp only
  intro K _ _ χ
  let _ : IsAffine U.toScheme := hA
  exact completeOpen_character_lift e I o U hU hC χ

end FLT.Mazur.EquivalenceRelationNormalizedFrames
