/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafImageOpenSections
public import FLT.Mazur.ModuleSheafPullbackMapRefinement

/-!
# Image-open local morphisms commute with refinement

Geometric refinement of a pullback morphism restricts its image-open local
morphism. The assertion holds on every subopen of the smaller image, which
is the compatibility needed by morphism gluing.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules

universe u

namespace FLT.Mazur.ModuleSheafOpenImmersionLocalHom

open ModuleSheafMorphismGluing

variable {X Y Z : Scheme.{u}} (i : Y ⟶ X) (t : Z ⟶ Y)
variable [IsOpenImmersion i] [IsOpenImmersion t]
variable {M N : X.Modules}

/-- A composite immersion has smaller image than its final factor. -/
lemma refinementRange_le : (t ≫ i).opensRange ≤ i.opensRange := by
  rw [Scheme.Hom.opensRange_comp]
  exact i.image_le_opensRange _

/-- Ordinary restriction refinement gives the same map on all smaller image subopens. -/
lemma ofRestriction_refine_app
    (a : (restrictFunctor i).obj M ⟶ (restrictFunctor i).obj N)
    (T : X.Opens) (hT : T ≤ (t ≫ i).opensRange) :
    localApp (ofRestriction (t ≫ i)
      ((restrictFunctorComp t i).hom.app M ≫ (restrictFunctor t).map a ≫
        (restrictFunctorComp t i).inv.app N)) hT =
      localApp (ofRestriction i a) (hT.trans (refinementRange_le i t)) := by
  obtain ⟨U, rfl⟩ : ∃ U : Z.Opens, (t ≫ i) ''ᵁ U = T :=
    ⟨(t ≫ i) ⁻¹ᵁ T, by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hT]⟩
  ext s
  rw [ofRestriction_app_image]
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    restrictFunctorComp_hom_app_app, restrictFunctorComp_inv_app_app]
  change res N _ (a.app (t ''ᵁ U) (res M _ s)) = _
  rw [← ofRestriction_app_image i a (t ''ᵁ U)]
  rw [← localApp_res, res_res]
  exact res_self M _ s |> congrArg (localApp (ofRestriction i a) _)

/-- Pullback refinement restricts the local morphism on every smaller image subopen. -/
lemma localHom_refine_app
    (a : (pullback i).obj M ⟶ (pullback i).obj N)
    (T : X.Opens) (hT : T ≤ (t ≫ i).opensRange) :
    localApp (localHom (t ≫ i)
      ((pullbackComp t i).inv.app M ≫ (pullback t).map a ≫
        (pullbackComp t i).hom.app N)) hT =
      localApp (localHom i a) (hT.trans (refinementRange_le i t)) := by
  unfold localHom
  rw [toRestriction_refine]
  exact ofRestriction_refine_app i t (toRestriction i a) T hT

end FLT.Mazur.ModuleSheafOpenImmersionLocalHom
