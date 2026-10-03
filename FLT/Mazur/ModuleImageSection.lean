/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSectionRegularity
public import FLT.Mazur.ModuleGlobalSectionExt

/-!
# Chart sections as sections on open images

The restriction-to-pullback comparison transports local sections to their
open images. Its composition coherence turns equality in a common pullback
module into equality of actual sheaf restrictions on a chart intersection.
-/

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X Y Z : Scheme.{u}}
/-- View a pulled-back chart section as a section on its open image. -/
def imageSection (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules)
    (s : Γ((pullback f).obj M, ⊤)) : Γ(M, f ''ᵁ ⊤) :=
  ((restrictFunctorIsoPullback f).inv.app M).app ⊤ s
/-- A global section becomes its sheaf restriction on the chart image. -/
lemma imageSection_pullGlobal (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules)
    (s : Γ(M, ⊤)) : imageSection f M (pullGlobal f M s) =
      M.presheaf.map (homOfLE (show f ''ᵁ ⊤ ≤ ⊤ from le_top)).op s := by
  rw [← pullGlobal_restrict]
  unfold imageSection
  exact congrArg (fun k ↦ k.app ⊤
    (M.presheaf.map (homOfLE (show f ''ᵁ ⊤ ≤ ⊤ from le_top)).op s))
    ((restrictFunctorIsoPullback f).hom_inv_id_app M)
/-- The image section recovers the original pulled-back chart section. -/
lemma pullGlobal_imageSection (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules)
    (s : Γ((pullback f).obj M, ⊤)) :
    ((restrictFunctorIsoPullback f).hom.app M).app ⊤ (imageSection f M s) = s :=
  congrArg (fun k ↦ k.app ⊤ s) ((restrictFunctorIsoPullback f).inv_hom_id_app M)
/-- The image of a composite open immersion lies in the outer chart image. -/
lemma image_comp_le (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f]
    [IsOpenImmersion g] : (f ≫ g) ''ᵁ ⊤ ≤ g ''ᵁ ⊤ := by
  rw [Scheme.Hom.comp_image]
  exact g.image_mono le_top
/-- Successive pullback becomes restriction on the composite open image. -/
lemma imageSection_comp (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f]
    [IsOpenImmersion g] (M : Z.Modules) (s : Γ((pullback g).obj M, ⊤)) :
    imageSection (f ≫ g) M
      (((pullbackComp f g).hom.app M).app ⊤ (pullGlobal f _ s)) =
    M.presheaf.map (homOfLE (image_comp_le f g)).op (imageSection g M s) := by
  apply (ConcreteCategory.bijective_of_isIso
    (((restrictFunctorIsoPullback (f ≫ g)).hom.app M).app ⊤)).injective
  rw [pullGlobal_imageSection]
  apply (ConcreteCategory.bijective_of_isIso
    (((pullbackComp f g).inv.app M).app ⊤)).injective
  have hh := congrArg (fun k ↦ (k.app M).app ⊤
    (M.presheaf.map (homOfLE (image_comp_le f g)).op (imageSection g M s)))
    (restrictFunctorIsoPullback_comp f g)
  change _ = ((pullbackComp f g).inv.app M).app ⊤
    (((restrictFunctorIsoPullback (f ≫ g)).hom.app M).app ⊤ _) at hh
  rw [← hh]
  have hc : ((pullbackComp f g).inv.app M).app ⊤
      (((pullbackComp f g).hom.app M).app ⊤ (pullGlobal f _ s)) =
      pullGlobal f _ s :=
    congrArg (fun k ↦ k.app ⊤ (pullGlobal f _ s)) ((pullbackComp f g).hom_inv_id_app M)
  rw [hc, ← pullGlobal_restrict]
  change ((restrictFunctorIsoPullback f).hom.app ((pullback g).obj M)).app ⊤ _ =
    ((restrictFunctorIsoPullback f).hom.app ((pullback g).obj M)).app ⊤ _
  apply congrArg (((restrictFunctorIsoPullback f).hom.app ((pullback g).obj M)).app ⊤)
  have hn := congrArg (fun k ↦ k (imageSection g M s))
    (((restrictFunctorIsoPullback g).hom.app M).mapPresheaf.naturality
      (homOfLE (show f ''ᵁ ⊤ ≤ ⊤ from le_top)).op)
  change _ = ((pullback g).obj M).presheaf.map _
    (((restrictFunctorIsoPullback g).hom.app M).app ⊤ (imageSection g M s)) at hn
  rw [pullGlobal_imageSection] at hn
  rw [← hn]
  change ((restrictFunctorIsoPullback g).hom.app M).app (f ''ᵁ ⊤) _ =
    ((restrictFunctorIsoPullback g).hom.app M).app (f ''ᵁ ⊤) _
  apply congrArg (((restrictFunctorIsoPullback g).hom.app M).app (f ''ᵁ ⊤))
  change M.presheaf.map _ _ = M.presheaf.map _ (M.presheaf.map _ _)
  rw [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp]
  rfl
/-- Equal scheme maps give the same restricted image section. -/
lemma imageSection_res_congr {f g : X ⟶ Y} [IsOpenImmersion f] [IsOpenImmersion g]
    (h : f = g) (M : Y.Modules) (s : Γ((pullback f).obj M, ⊤)) (U : Y.Opens)
    (hf : U ≤ f ''ᵁ ⊤) (hg : U ≤ g ''ᵁ ⊤) :
    M.presheaf.map (homOfLE hf).op (imageSection f M s) =
      M.presheaf.map (homOfLE hg).op
        (imageSection g M (((pullbackCongr h).hom.app M).app ⊤ s)) := by
  subst g
  rfl
/-- Common pullback equality gives equality on the actual chart intersection. -/
lemma pullOverlap_compatible {W : Scheme.{u}}
    (f : X ⟶ Y) (j : Y ⟶ Z) (g : X ⟶ W) (k : W ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion j] [IsOpenImmersion g] [IsOpenImmersion k]
    (h : f ≫ j = g ≫ k) (M : Z.Modules)
    (s : Γ((pullback j).obj M, ⊤)) (t : Γ((pullback k).obj M, ⊤))
    (hab : pullOverlap f j M s = pullOverlapAlong g k (f ≫ j) h.symm M t)
    (hcover : j ''ᵁ ⊤ ⊓ k ''ᵁ ⊤ ≤ (f ≫ j) ''ᵁ ⊤) :
    M.presheaf.map (homOfLE (inf_le_left : j ''ᵁ ⊤ ⊓ k ''ᵁ ⊤ ≤ j ''ᵁ ⊤)).op
      (imageSection j M s) =
    M.presheaf.map (homOfLE (inf_le_right : j ''ᵁ ⊤ ⊓ k ''ᵁ ⊤ ≤ k ''ᵁ ⊤)).op
      (imageSection k M t) := by
  have hc : j ''ᵁ ⊤ ⊓ k ''ᵁ ⊤ ≤ (g ≫ k) ''ᵁ ⊤ := by simpa only [h] using hcover
  have hh := imageSection_res_congr h.symm M (pullOverlap g k M t) _ hc hcover
  change _ = M.presheaf.map (homOfLE hcover).op
    (imageSection (f ≫ j) M (pullOverlapAlong g k (f ≫ j) h.symm M t)) at hh
  rw [← hab] at hh
  change M.presheaf.map _ (imageSection (g ≫ k) M
    (((pullbackComp g k).hom.app M).app ⊤ (pullGlobal g _ t))) =
    M.presheaf.map _ (imageSection (f ≫ j) M
    (((pullbackComp f j).hom.app M).app ⊤ (pullGlobal f _ s))) at hh
  rw [imageSection_comp, imageSection_comp] at hh
  simpa only [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp, ← op_comp,
    homOfLE_comp] using hh.symm
end FLT.Mazur.FCurve
