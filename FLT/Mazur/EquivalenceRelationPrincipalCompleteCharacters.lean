/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteInvariantPrincipal
public import FLT.Mazur.EquivalenceRelationInvariantCharacterArrows
public import FLT.Mazur.SchemeFiniteGroupPrincipalCharacterLifts

/-!
# All full characters on a constructed complete principal neighborhood

One interior complete point constructs a single invariant denominator valid
over every algebraically closed field. Every character where it is nonzero
has a complete lift, and every other lift has a constructed original arrow.
The character need not have the same scalar restriction as the initial point.
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
local notation "u" w => sourceCharacterMap (X := B.toScheme) w ≫ B.ι
attribute [local irreducible] source action restrictedAction completeInterior Complete

/-- One denominator controls all full characters, not only the initial scalar fiber. -/
theorem exists_complete_principal_character_neighborhood (x : B.toScheme)
    (hx : B.ι x ∈ completeInterior (p := p) (q := q) I o) :
    ∃ t : invariantCoordinates ρ,
      x ∈ B.toScheme.basicOpen t.val ∧
      ∀ {K : Type} [Field K] [IsAlgClosed K]
        (χ : invariantCoordinates ρ →+* K), χ t ≠ 0 →
      ∃ w : Γ(B.toScheme, ⊤) →+* K,
        (∀ r : invariantCoordinates ρ, w r.val = χ r) ∧
        (u w) default ∈ completeInterior (p := p) (q := q) I o ∧
        Complete I o (u w) ∧
        ∀ v : Γ(B.toScheme, ⊤) →+* K,
          (∀ r : invariantCoordinates ρ, v r.val = χ r) →
          (u v) default ∈ completeInterior (p := p) (q := q) I o ∧
          Complete I o (u v) ∧
          ∃! a : Spec (.of K) ⟶ D,
            a ≫ p = (u w) ≫ first p q I o ∧
            a ≫ q = (u v) ≫ first p q I o := by
  obtain ⟨t, ht, hC⟩ := exists_complete_invariant_principal e I o B hB x hx
  refine ⟨t, ht, ?_⟩
  intro K _ _ χ hχ
  obtain ⟨w, _, hw, _, _⟩ := exists_principal_sourceCharacter_lift ρ t χ hχ
  have hi (v : Γ(B.toScheme, ⊤) →+* K)
      (hv : ∀ r : invariantCoordinates ρ, v r.val = χ r) :
      (u v) default ∈ completeInterior (p := p) (q := q) I o := by
    exact hC _ ((sourceCharacterMap_mem_invariant_basicOpen ρ v t).mpr (by rwa [hv t]))
  have hc (v : Γ(B.toScheme, ⊤) →+* K)
      (hv : ∀ r : invariantCoordinates ρ, v r.val = χ r) : Complete I o (u v) :=
    (complete_iff_mem_completePointLocus I o (u v)).mpr
      (completeInterior_subset I o (hi v hv))
  refine ⟨w, hw, hi w hw, hc w hw, fun v hv ↦ ⟨hi v hv, hc v hv, ?_⟩⟩
  exact invariant_character_original_arrow e I o B hB w v
    (fun r ↦ (hw r).trans (hv r).symm)

end FLT.Mazur.EquivalenceRelationNormalizedFrames
