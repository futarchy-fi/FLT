/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocallyRingedOpenImage

/-!
# Inclusions between actual locally ringed restrictions

Nested open subsets induce canonical locally ringed inclusions. The maps retain
both the underlying subtype inclusion and the original sheaf restriction.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
universe u
namespace FLT.Mazur.LocallyRingedOpenInclusion
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (X : LocallyRingedSpace.{u}) {V W : Opens X} (h : V ≤ W)

/-- The canonical inclusion of two actual open restrictions. -/
def inclusion : X.restrict V.isOpenEmbedding ⟶ X.restrict W.isOpenEmbedding :=
  LocallyRingedSpace.IsOpenImmersion.lift (X.ofRestrict W.isOpenEmbedding)
    (X.ofRestrict V.isOpenEmbedding) (by
      change Set.range (Subtype.val : V → X) ⊆ Set.range (Subtype.val : W → X)
      rintro _ ⟨x, rfl⟩
      exact ⟨⟨x.val, h x.property⟩, rfl⟩)

/-- The inclusion preserves the ambient restriction morphisms. -/
@[reassoc] theorem inclusion_comp :
    inclusion X h ≫ X.ofRestrict W.isOpenEmbedding = X.ofRestrict V.isOpenEmbedding :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _

/-- Its underlying map is the original subtype inclusion. -/
theorem inclusion_base (x : V) : (inclusion X h).base x = ⟨x.val, h x.property⟩ := by
  apply Subtype.ext
  exact congrArg (fun f => f.base x) (inclusion_comp X h)

/-- Nested restrictions are themselves open immersions. -/
instance inclusion_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion (inclusion X h) := by
  unfold inclusion LocallyRingedSpace.IsOpenImmersion.lift
  infer_instance

/-- Restriction along an identity inclusion is the identity morphism. -/
theorem inclusion_refl : inclusion X (le_refl V) = 𝟙 _ := by
  rw [← cancel_mono (X.ofRestrict V.isOpenEmbedding), inclusion_comp, Category.id_comp]

/-- Successive open inclusions agree with the direct inclusion. -/
@[reassoc] theorem inclusion_trans {T : Opens X} (k : W ≤ T) :
    inclusion X h ≫ inclusion X k = inclusion X (h.trans k) := by
  rw [← cancel_mono (X.ofRestrict T.isOpenEmbedding), Category.assoc,
    inclusion_comp, inclusion_comp, inclusion_comp]

/-- Global sections of an open restriction identify with sections on that open. -/
def sectionsIso (V : Opens X) :
    LocallyRingedSpace.Γ.obj (op (X.restrict V.isOpenEmbedding)) ≅
      X.presheaf.obj (op V) :=
  X.presheaf.mapIso (eqToIso (congrArg op (Opens.isOpenEmbedding_obj_top V)))

/-- Pullback along the inclusion is the original restriction of sections. -/
theorem inclusion_sections :
    (sectionsIso X W).inv ≫ LocallyRingedSpace.Γ.map (inclusion X h).op =
      X.presheaf.map (homOfLE h).op ≫ (sectionsIso X V).inv := by
  have H := PresheafedSpace.congr_app
    (congrArg LocallyRingedSpace.Hom.toHom (inclusion_comp X h)) (op W)
  change (X.ofRestrict W.isOpenEmbedding).c.app (op W) ≫
    (inclusion X h).c.app (op ((Opens.map
      (X.ofRestrict W.isOpenEmbedding).base).obj W)) = _ at H
  have ht : (Opens.map (X.ofRestrict W.isOpenEmbedding).base).obj W = ⊤ :=
    Opens.inclusion'_map_eq_top W
  have hs : (sectionsIso X W).inv =
      (X.ofRestrict W.isOpenEmbedding).c.app (op W) ≫
        (X.restrict W.isOpenEmbedding).presheaf.map (eqToHom (congrArg op ht)) := by
    change X.presheaf.map _ = X.presheaf.map _ ≫ X.presheaf.map _
    rw [← Functor.map_comp]
    congr 1
  rw [hs, LocallyRingedSpace.Γ_map_op, Category.assoc,
    (inclusion X h).c.naturality (eqToHom (congrArg op ht)), ← Category.assoc, H]
  change (X.presheaf.map _ ≫ X.presheaf.map _) ≫ X.presheaf.map _ =
    X.presheaf.map _ ≫ X.presheaf.map _
  simp only [← Functor.map_comp]
  congr 1

end FLT.Mazur.LocallyRingedOpenInclusion
