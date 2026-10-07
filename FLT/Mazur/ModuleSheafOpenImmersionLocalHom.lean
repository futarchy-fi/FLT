/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafMorphismGluing

/-!
# Local morphisms from open-immersion pullbacks

A map between pullbacks along an open immersion determines a linear map
on the slice over its image. The construction retains the original map
and is injective, so gluing on image opens recovers the supplied pullbacks.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules

universe u

namespace FLT.Mazur.ModuleSheafOpenImmersionLocalHom

variable {X Y : Scheme.{u}} (i : Y ⟶ X) [IsOpenImmersion i]
variable {M N : X.Modules}

/-- The restriction adjunction unit is invertible on the image of the immersion. -/
instance unit_over_isIso (M : X.Modules) :
    IsIso (((restrictAdjunction i).unit.app M).over i.opensRange) := by
  rw [← isIso_iff_of_reflects_iso _
    (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _),
    NatTrans.isIso_iff_isIso_app]
  intro V
  change IsIso (M.presheaf.map (homOfLE
    (i.image_preimage_le V.unop.left)).op)
  have he : i ''ᵁ (i ⁻¹ᵁ V.unop.left) = V.unop.left := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
      inf_eq_right.mpr (leOfHom V.unop.hom)]
  have hh : homOfLE (i.image_preimage_le V.unop.left) = eqToHom he :=
    Subsingleton.elim _ _
  rw [hh]
  infer_instance

/-- Extend a restriction morphism to the slice over the image open. -/
def ofRestriction (a : (restrictFunctor i).obj M ⟶ (restrictFunctor i).obj N) :
    M.over i.opensRange ⟶ N.over i.opensRange :=
  ((restrictAdjunction i).unit.app M).over i.opensRange ≫
    ((pushforward i).map a).over i.opensRange ≫
      inv (((restrictAdjunction i).unit.app N).over i.opensRange)

/-- For a global map the construction is exactly its slice restriction. -/
lemma ofRestriction_map (a : M ⟶ N) :
    ofRestriction i ((restrictFunctor i).map a) = a.over i.opensRange := by
  apply (cancel_mono (((restrictAdjunction i).unit.app N).over i.opensRange)).mp
  simp only [ofRestriction, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  exact (congrArg (fun b ↦ b.over i.opensRange)
    ((restrictAdjunction i).unit.naturality a)).symm

/-- Restricting a pushforward morphism to its image loses no information. -/
lemma pushforward_over_injective {P Q : Y.Modules} :
    Function.Injective (fun a : P ⟶ Q ↦ ((pushforward i).map a).over i.opensRange) := by
  intro a b h
  apply Scheme.Modules.hom_ext
  intro U
  have he : i ⁻¹ᵁ (i ''ᵁ U) = U := i.preimage_image_eq U
  have hh := congrArg (fun c ↦ c.val.app
    (op (Over.mk (homOfLE (i.image_le_opensRange U)))) ) h
  have hab : a.app (i ⁻¹ᵁ (i ''ᵁ U)) = b.app (i ⁻¹ᵁ (i ''ᵁ U)) := by
    exact congrArg (fun c ↦ AddCommGrpCat.ofHom c.hom.toAddMonoidHom) hh
  exact he ▸ hab

/-- The local extension determines the original restriction morphism uniquely. -/
lemma ofRestriction_injective : Function.Injective (ofRestriction i (M := M) (N := N)) := by
  intro a b h
  apply pushforward_over_injective i
  apply (cancel_epi (((restrictAdjunction i).unit.app M).over i.opensRange)).mp
  apply (cancel_mono (inv (((restrictAdjunction i).unit.app N).over i.opensRange))).mp
  simpa only [ofRestriction, Category.assoc] using h

/-- Change a genuine pullback map to a restriction map through the canonical comparison. -/
def toRestriction (a : (pullback i).obj M ⟶ (pullback i).obj N) :
    (restrictFunctor i).obj M ⟶ (restrictFunctor i).obj N :=
  (restrictFunctorIsoPullback i).hom.app M ≫ a ≫
    (restrictFunctorIsoPullback i).inv.app N

/-- Pullback of a global map becomes its ordinary restriction. -/
lemma toRestriction_map (a : M ⟶ N) :
    toRestriction i ((pullback i).map a) = (restrictFunctor i).map a := by
  rw [toRestriction, ← (restrictFunctorIsoPullback i).hom.naturality_assoc]
  simp only [Iso.hom_inv_id_app, Category.comp_id]

/-- Changing pullback conventions preserves all information. -/
lemma toRestriction_injective : Function.Injective (toRestriction i (M := M) (N := N)) := by
  intro a b h
  apply (cancel_epi ((restrictFunctorIsoPullback i).hom.app M)).mp
  apply (cancel_mono ((restrictFunctorIsoPullback i).inv.app N)).mp
  exact h

/-- The linear local morphism on the image open attached to a pullback morphism. -/
def localHom (a : (pullback i).obj M ⟶ (pullback i).obj N) :
    M.over i.opensRange ⟶ N.over i.opensRange :=
  ofRestriction i (toRestriction i a)

/-- The image-open local morphism uniquely determines its original pullback map. -/
lemma localHom_injective : Function.Injective (localHom i (M := M) (N := N)) :=
  (ofRestriction_injective i).comp (toRestriction_injective i)

/-- Global pullback maps restrict to the original local module morphisms. -/
lemma localHom_map (a : M ⟶ N) :
    localHom i ((pullback i).map a) = a.over i.opensRange := by
  rw [localHom, toRestriction_map, ofRestriction_map]

end FLT.Mazur.ModuleSheafOpenImmersionLocalHom
