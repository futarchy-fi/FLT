/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFiniteGroupGeometricTests
public import FLT.Mazur.FiniteGroupFieldPointOrbits

/-!
# Actual scheme arrows from invariant character equality

The polynomial orbit theorem constructs a single group element over the
unchanged field. Its action identifies the entire scheme morphisms, including
their residue-field maps, rather than just their underlying points.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open FLT.Mazur.SchemeCoordinateAction
namespace FLT.Mazur.SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {G : Type} [Group G] {X : Scheme} [IsAffine X]
  (ρ : G →* Aut X) {K : Type} [Field K]

/-- Realizing a pulled-back character commutes with the actual scheme action. -/
theorem sourceCharacterMap_action (w : Γ(X, ⊤) →+* K) (g : G) :
    sourceCharacterMap (w.comp (coordinateHom ρ g⁻¹)) =
      sourceCharacterMap w ≫ (ρ g).hom := by
  apply (cancel_mono X.toSpecΓ).mp
  have hw (v : Γ(X, ⊤) →+* K) :
      sourceCharacterMap v ≫ X.toSpecΓ = Spec.map (CommRingCat.ofHom v) := by
    change (Spec.map (CommRingCat.ofHom v) ≫ X.isoSpec.inv) ≫ X.isoSpec.hom = _
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [Category.assoc, toSpecΓ_equivariant, ← Category.assoc, hw, hw]
  exact Spec.map_comp _ _

variable [Finite G]

/-- Equality on every invariant constructs one actual group arrow over the same field. -/
theorem sourceCharacterMap_orbit_of_invariants
    (v w : Γ(X, ⊤) →+* K)
    (h : ∀ t : invariantCoordinates ρ, v t.val = w t.val) :
    ∃ g : G, sourceCharacterMap v ≫ (ρ g).hom = sourceCharacterMap w := by
  let _ := coordinateAction ρ
  have he : v.comp (FiniteGroupQuotient.inclusion G Γ(X, ⊤)) =
      w.comp (FiniteGroupQuotient.inclusion G Γ(X, ⊤)) := RingHom.ext h
  obtain ⟨g, hg⟩ := FiniteGroupQuotient.exists_ringHom_orbit G Γ(X, ⊤) v w he
  refine ⟨g⁻¹, ?_⟩
  rw [← sourceCharacterMap_action, inv_inv]
  exact congrArg sourceCharacterMap hg.symm

end FLT.Mazur.SchemeFiniteGroupQuotient
