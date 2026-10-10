/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoherentSubmoduleGluing

/-!
# Local detection of equality of original chart subobjects

Equality of transported subobjects near every point implies equality on
the entire overlap. Slice evaluation avoids any choice of global frames
or an affineness assumption on the intersection itself.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.CoherentSubmoduleGluing
open ModuleSheafMorphismGluing ModuleSubobjectCoverEquality
variable {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens}
variable {L : U.toScheme.Modules} {N : V.toScheme.Modules}
variable (a : L ⟶ M.restrict U.ι) (b : N ⟶ M.restrict V.ι) [Mono a] [Mono b]

/-- Equality of transported subobjects gives actual section preimages on every smaller open. -/
lemma local_preimage_of_subobject_eq {T S : X.Opens} (hU : T ≤ U) (hV : T ≤ V)
    (hS : S ≤ T)
    (he : Subobject.mk (restrictionEquiv T (inclusionOn M a hU)) =
      Subobject.mk (restrictionEquiv T (inclusionOn M b hV)))
    (v : Γ((pushforward U.ι).obj L, S)) :
    ∃ w, localApp (inclusionOn M b hV) hS w = localApp (inclusionOn M a hU) hS v := by
  let c := (restrictionEquiv T).symm (Subobject.ofMkLEMk _ _ he.le)
  have hc : c ≫ inclusionOn M b hV = inclusionOn M a hU := by
    apply (restrictionEquiv T).injective
    rw [restrictionEquiv_comp]
    dsimp only [c]
    rw [Equiv.apply_symm_apply]
    exact Subobject.ofMkLEMk_comp he.le
  exact ⟨localApp c hS v, congrArg (fun f ↦ localApp f hS v) hc⟩

/-- Pointwise local equality determines the actual original overlap subobjects. -/
lemma subobject_eq_of_local {O : X.Opens} (hOU : O ≤ U) (hOV : O ≤ V)
    (h : ∀ x : X, x ∈ O →
      ∃ (T : X.Opens) (hU : T ≤ U) (hV : T ≤ V), x ∈ T ∧
        Subobject.mk (restrictionEquiv T (inclusionOn M a hU)) =
          Subobject.mk (restrictionEquiv T (inclusionOn M b hV))) :
    Subobject.mk (restrictionEquiv O (inclusionOn M a hOU)) =
      Subobject.mk (restrictionEquiv O (inclusionOn M b hOV)) := by
  have go {U V : X.Opens} (hOU : O ≤ U) (hOV : O ≤ V)
      {A : U.toScheme.Modules} {B : V.toScheme.Modules}
      (a : A ⟶ M.restrict U.ι) (b : B ⟶ M.restrict V.ι) [Mono a] [Mono b]
      (h : ∀ x : X, x ∈ O →
        ∃ (T : X.Opens) (hU : T ≤ U) (hV : T ≤ V), x ∈ T ∧
          Subobject.mk (restrictionEquiv T (inclusionOn M a hU)) =
            Subobject.mk (restrictionEquiv T (inclusionOn M b hV))) :
      ∀ (Q : O.toScheme.Opens) (v : Γ(((pushforward U.ι).obj A).restrict O.ι, Q)),
        ∃ w, (restrictionEquiv O (inclusionOn M b hOV)).app Q w =
          (restrictionEquiv O (inclusionOn M a hOU)).app Q v := by
    apply sections_of_local
    intro Q v x hx
    obtain ⟨T, hU, hV, hxT, he⟩ := h (O.ι x) x.property
    let P := Q ⊓ O.ι ⁻¹ᵁ T
    have hP : O.ι ''ᵁ P ≤ T := by
      exact (O.ι.image_mono inf_le_right).trans (O.ι.image_preimage_le T)
    refine ⟨P, inf_le_left, ⟨hx, hxT⟩, ?_⟩
    obtain ⟨w, hw⟩ := local_preimage_of_subobject_eq M a b hU hV hP he
      (res (((pushforward U.ι).obj A).restrict O.ι) inf_le_left v)
    refine ⟨w, ?_⟩
    change localApp (inclusionOn M b hOV) (O.ι_image_le P) w =
      localApp (inclusionOn M a hOU) (O.ι_image_le P) _
    rw [inclusionOn_localApp M b hOV hV (O.ι_image_le P) hP,
      inclusionOn_localApp M a hOU hU (O.ι_image_le P) hP]
    exact hw
  apply le_antisymm
  · exact Subobject.mk_le_mk_of_comm (factor _ _ (go hOU hOV a b h)) (factor_comp _ _ _)
  · have h' : ∀ x : X, x ∈ O →
        ∃ (T : X.Opens) (hV : T ≤ V) (hU : T ≤ U), x ∈ T ∧
          Subobject.mk (restrictionEquiv T (inclusionOn M b hV)) =
            Subobject.mk (restrictionEquiv T (inclusionOn M a hU)) := by
      intro x hx
      obtain ⟨T, hU, hV, hxT, he⟩ := h x hx
      exact ⟨T, hV, hU, hxT, he.symm⟩
    exact Subobject.mk_le_mk_of_comm (factor _ _ (go hOV hOU b a h')) (factor_comp _ _ _)

end FLT.Mazur.CoherentSubmoduleGluing
