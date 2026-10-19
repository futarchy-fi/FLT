/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteInterior
public import FLT.Mazur.SchemeFiniteGroupInvariantPrincipal

/-!
# Principal full-character neighborhoods of complete frames

Inside an independently fixed stable affine chart, an interior complete point
constructs an invariant denominator. Its entire principal source open consists
of interior complete frames, with the original size and label unchanged.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (B : (source p q I o).Opens)
  (hB : ∀ g : Equiv.Perm I, (action e I o g).hom ⁻¹ᵁ B = B)
  [IsAffine B.toScheme]
local notation "ρ" => restrictedAction (action e I o) B hB
attribute [local irreducible] source action restrictedAction completeInterior

/-- Construct a full invariant denominator whose whole principal open is complete. -/
theorem exists_complete_invariant_principal (x : B.toScheme)
    (hx : B.ι x ∈ completeInterior (p := p) (q := q) I o) :
    ∃ t : invariantCoordinates ρ,
      x ∈ B.toScheme.basicOpen t.val ∧
      ∀ y ∈ B.toScheme.basicOpen t.val,
        B.ι y ∈ completeInterior (p := p) (q := q) I o := by
  let O := B.ι ⁻¹ᵁ completeInterior (p := p) (q := q) I o
  have hO : ∀ (g : Equiv.Perm I) (y : B.toScheme), y ∈ O → (ρ g).hom y ∈ O := by
    intro g y hy
    change B.ι ((ρ g).hom y) ∈ completeInterior (p := p) (q := q) I o
    rw [← Scheme.Hom.comp_apply, restrictedAction_hom_ι, Scheme.Hom.comp_apply]
    have he := congrArg (fun U : (source p q I o).Opens ↦ B.ι y ∈ U)
      (completeInterior_action_invariant e I o g)
    exact he.to_iff.mpr hy
  obtain ⟨t, ht, htO⟩ := exists_invariant_principal ρ O hO x hx
  exact ⟨t, ht, htO⟩

end FLT.Mazur.EquivalenceRelationNormalizedFrames
