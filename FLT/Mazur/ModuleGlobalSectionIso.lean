/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleGlobalSectionExt
public import FLT.Mazur.ModuleSectionRegularity

/-!
# Section pullback across isomorphisms

The actual semilinear pullback map is bijective along a scheme isomorphism.
Consequently surjectivity of restriction is invariant under an isomorphism
of its source, with the canonical pullback comparisons.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.FCurve

variable {X Y Z : Scheme.{u}}

/-- Pullback along an isomorphism gives a bijection on actual global sections. -/
lemma pullGlobal_bijective_of_isIso (f : X ⟶ Y) [IsIso f] (M : Y.Modules) :
    Function.Bijective (pullGlobal f M) := by
  have ht : f ''ᵁ ⊤ = ⊤ := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]
  have hi : IsIso (homOfLE (show f ''ᵁ ⊤ ≤ ⊤ from le_top)) := by
    have he : homOfLE (show f ''ᵁ ⊤ ≤ ⊤ from le_top) = eqToHom ht := Subsingleton.elim _ _
    rw [he]
    infer_instance
  have hb := (ConcreteCategory.bijective_of_isIso
    (((restrictFunctorIsoPullback f).hom.app M).app ⊤)).comp
      (ConcreteCategory.bijective_of_isIso
        (M.presheaf.map (homOfLE (show f ''ᵁ ⊤ ≤ ⊤ from le_top)).op))
  simpa only [Function.comp_def, pullGlobal_restrict] using hb

/-- A source isomorphism can be removed from a surjective section restriction. -/
lemma pullGlobal_surjective_of_comp_iso (f : X ⟶ Y) [IsIso f] (g : Y ⟶ Z)
    (M : Z.Modules) (h : Function.Surjective (pullGlobal (f ≫ g) M)) :
    Function.Surjective (pullGlobal g M) := by
  intro s
  obtain ⟨t, ht⟩ := h (((pullbackComp f g).hom.app M).app ⊤
    (pullGlobal f ((pullback g).obj M) s))
  refine ⟨t, (pullGlobal_bijective_of_isIso f _).injective ?_⟩
  rw [← pullGlobal_comp, ht]
  exact ConcreteCategory.congr_hom
    (congrArg (fun k ↦ k.app ⊤) ((pullbackComp f g).hom_inv_id_app M)) _

/-- Equal morphisms have equally surjective pullback maps on global sections. -/
lemma pullGlobal_surjective_congr {f g : X ⟶ Y} (h : f = g) (M : Y.Modules) :
    Function.Surjective (pullGlobal f M) ↔ Function.Surjective (pullGlobal g M) := by
  subst g
  rfl

end FLT.Mazur.FCurve
