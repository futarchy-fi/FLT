/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafOpenImmersionLocalHom

/-!
# Sections of image-open module morphisms

The extension of a restriction morphism is characterized by the restriction
adjunction unit on every subopen of the image. Those unit maps are invertible,
so this characterization detects equality without choosing section representatives.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules

universe u

namespace FLT.Mazur.ModuleSheafOpenImmersionLocalHom

open ModuleSheafMorphismGluing

variable {X Y : Scheme.{u}} (i : Y ⟶ X) [IsOpenImmersion i]
variable {M N : X.Modules}

/-- The image-preimage restriction is invertible on any subopen of the image. -/
lemma imagePreimage_isIso (M : X.Modules) (U : X.Opens) (hU : U ≤ i.opensRange) :
    IsIso (M.presheaf.map (homOfLE (i.image_preimage_le U)).op) := by
  have he : i ''ᵁ (i ⁻¹ᵁ U) = U := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hU]
  have hh : homOfLE (i.image_preimage_le U) = eqToHom he := Subsingleton.elim _ _
  rw [hh]
  infer_instance

/-- The local extension commutes with the restriction adjunction unit. -/
lemma ofRestriction_unit (a : (restrictFunctor i).obj M ⟶ (restrictFunctor i).obj N) :
    ofRestriction i a ≫ ((restrictAdjunction i).unit.app N).over i.opensRange =
      ((restrictAdjunction i).unit.app M).over i.opensRange ≫
        ((pushforward i).map a).over i.opensRange := by
  simp only [ofRestriction, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- On sections, the local extension is the original map conjugated by unit restrictions. -/
lemma ofRestriction_app_unit
    (a : (restrictFunctor i).obj M ⟶ (restrictFunctor i).obj N)
    (U : X.Opens) (hU : U ≤ i.opensRange) (s : Γ(M, U)) :
    res N (i.image_preimage_le U) (localApp (ofRestriction i a) hU s) =
      a.app (i ⁻¹ᵁ U) (res M (i.image_preimage_le U) s) := by
  exact congrArg (fun c ↦ c.val.app (op (Over.mk (homOfLE hU))) s)
    (ofRestriction_unit i a)

/-- Equality after the unit restriction detects equality of local section maps. -/
lemma localApp_eq_of_unit {U V : X.Opens}
    (a : M.over U ⟶ N.over U) (b : M.over V ⟶ N.over V)
    (T : X.Opens) (hT : T ≤ i.opensRange) (hU : T ≤ U) (hV : T ≤ V)
    (h : ∀ s : Γ(M, T),
      res N (i.image_preimage_le T) (localApp a hU s) =
        res N (i.image_preimage_le T) (localApp b hV s)) :
    localApp a hU = localApp b hV := by
  let _ := imagePreimage_isIso i N T hT
  ext s
  exact (ConcreteCategory.bijective_of_isIso
    (N.presheaf.map (homOfLE (i.image_preimage_le T)).op)).injective (h s)

/-- On image opens, extension recovers the original restriction morphism on sections. -/
lemma ofRestriction_app_image
    (a : (restrictFunctor i).obj M ⟶ (restrictFunctor i).obj N)
    (U : Y.Opens) (s : Γ((restrictFunctor i).obj M, U)) :
    localApp (ofRestriction i a) (i.image_le_opensRange U) s = a.app U s := by
  let _ := imagePreimage_isIso i N (i ''ᵁ U) (i.image_le_opensRange U)
  apply (ConcreteCategory.bijective_of_isIso
    (N.presheaf.map (homOfLE (i.image_preimage_le (i ''ᵁ U))).op)).injective
  rw [ofRestriction_app_unit]
  exact congrArg (fun c ↦ c s)
    (a.mapPresheaf.naturality (eqToHom (i.preimage_image_eq U)).op)

end FLT.Mazur.ModuleSheafOpenImmersionLocalHom
