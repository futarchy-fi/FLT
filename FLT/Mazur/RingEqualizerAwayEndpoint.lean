/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RingEqualizerLocalDescent
/-!
# The normalization away from the endpoint image

Inverting a function whose endpoint value is zero makes the endpoint ring
trivial. The localized normalization then becomes an isomorphism.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace FLT.Mazur.RingEqualizerAwayEndpoint
open RingEqualizerLocalDescent RingEqualizerLocalization
variable {C D : Type u} [CommRing C] [CommRing D] (f g : C →+* D) (s : f.eqLocus g)
/-- The localized normalization is an isomorphism away from the endpoints. -/
theorem branch_isIso (hs : f s.val = 0) : IsIso (branch f g s) := by
  have hu : IsUnit (0 : Localization.Away (f s.val)) := by
    simpa only [hs, map_zero] using
      (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (f s.val)) (f s.val))
  let : Subsingleton (Localization.Away (f s.val)) :=
    subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hu)
  have hb : Function.Bijective (E f g s).subtype :=
    ⟨Subtype.val_injective, fun z ↦ ⟨⟨z, Subsingleton.elim _ _⟩, rfl⟩⟩
  let e := RingEquiv.ofBijective (E f g s).subtype hb
  change IsIso (Spec.map (CommRingCat.ofHom e.toRingHom))
  exact inferInstanceAs (IsIso (Scheme.Spec.mapIso e.toCommRingCatIso.op).hom)

/-- Every normalization morphism descends away from the endpoints. -/
theorem exists_desc {Y : Scheme.{u}} (h : Spec (.of C) ⟶ Y) (hs : f s.val = 0) :
    ∃ d : Spec (.of (E f g s)) ⟶ Y, branch f g s ≫ d = branchOpen f g s ≫ h := by
  let := branch_isIso f g s hs
  exact ⟨inv (branch f g s) ≫ branchOpen f g s ≫ h, by simp⟩
end FLT.Mazur.RingEqualizerAwayEndpoint
