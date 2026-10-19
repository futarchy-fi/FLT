/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFiniteGroupCharacterLifts
public import FLT.Mazur.SchemeFiniteGroupInvariantPrincipal

/-!
# Full invariant characters lift inside prescribed principal charts

A nonzero invariant value forces every lift into the actual principal source
open. Algebraically closed characters have constructed lifts over the same
field, preserving the entire quotient morphism and the original inclusion.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {G : Type} [Group G] [Finite G] {X : Scheme} [IsAffine X]
  (ρ : G →* Aut X) {K : Type} [Field K]

omit [Finite G] in
/-- Nonvanishing of a full invariant is exactly membership in its source principal open. -/
theorem sourceCharacterMap_mem_invariant_basicOpen
    (w : Γ(X, ⊤) →+* K) (t : invariantCoordinates ρ) :
    sourceCharacterMap w default ∈ X.basicOpen t.val ↔ w t.val ≠ 0 := by
  rw [← quotientMap_preimage_basicOpen ρ t]
  change (sourceCharacterMap w ≫ quotientMap ρ) default ∈ PrimeSpectrum.basicOpen t ↔ _
  rw [sourceCharacterMap_quotient]
  rfl

variable [IsAlgClosed K]

/-- Construct an exact full-character lift inside the prescribed original principal source. -/
theorem exists_principal_sourceCharacter_lift (t : invariantCoordinates ρ)
    (χ : invariantCoordinates ρ →+* K) (ht : χ t ≠ 0) :
    ∃ (w : Γ(X, ⊤) →+* K) (z : Spec (.of K) ⟶ (X.basicOpen t.val).toScheme),
      (∀ r : invariantCoordinates ρ, w r.val = χ r) ∧
      z ≫ (X.basicOpen t.val).ι = sourceCharacterMap w ∧
      z ≫ (X.basicOpen t.val).ι ≫ quotientMap ρ = Spec.map (CommRingCat.ofHom χ) := by
  obtain ⟨w, hw⟩ := exists_sourceCharacter_lift ρ χ
  have hx : sourceCharacterMap w default ∈ X.basicOpen t.val :=
    (sourceCharacterMap_mem_invariant_basicOpen ρ w t).mpr (by rwa [hw t])
  have hr : Set.range (sourceCharacterMap w) ⊆ Set.range (X.basicOpen t.val).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨a, rfl⟩
    rwa [Subsingleton.elim a default]
  let z := IsOpenImmersion.lift (X.basicOpen t.val).ι (sourceCharacterMap w) hr
  have hz : z ≫ (X.basicOpen t.val).ι = sourceCharacterMap w :=
    IsOpenImmersion.lift_fac _ _ _
  refine ⟨w, z, hw, hz, ?_⟩
  rw [← Category.assoc, hz, sourceCharacterMap_quotient]
  apply congrArg Spec.map
  ext r
  exact hw r

end FLT.Mazur.SchemeFiniteGroupQuotient
