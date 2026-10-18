/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Limits

/-!
# A pair of disjoint open charts

The coproduct of two disjoint open charts embeds as their entire open union.
This packages two separate boundary components into a single gluing arrow.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.SchemeDisjointOpenPair
set_option backward.isDefEq.respectTransparency false
universe u
variable {A B X : Scheme.{u}} (f : A ⟶ X) (g : B ⟶ X)

/-- Every point of a scheme coproduct lies in one of its two full charts. -/
theorem charts_cover (z : (A ⨿ B : Scheme.{u})) :
    (∃ a, (coprod.inl : A ⟶ A ⨿ B) a = z) ∨
      ∃ b, (coprod.inr : B ⟶ A ⨿ B) b = z := by
  obtain ⟨z, rfl⟩ := (coprodMk A B).surjective z
  cases z with
  | inl a => exact Or.inl ⟨a, (coprodMk_inl A B a).symm⟩
  | inr b => exact Or.inr ⟨b, (coprodMk_inr A B b).symm⟩

/-- The coproduct map covers exactly the union of the two original full images. -/
theorem desc_range : Set.range (coprod.desc f g) = Set.range f ∪ Set.range g := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    rcases charts_cover x with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · exact Or.inl ⟨a, (congrArg (fun h ↦ h a) (coprod.inl_desc f g)).symm⟩
    · exact Or.inr ⟨b, (congrArg (fun h ↦ h b) (coprod.inr_desc f g)).symm⟩
  · rintro (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · exact ⟨(coprod.inl : A ⟶ A ⨿ B) a, congrArg (fun h ↦ h a) (coprod.inl_desc f g)⟩
    · exact ⟨(coprod.inr : B ⟶ A ⨿ B) b, congrArg (fun h ↦ h b) (coprod.inr_desc f g)⟩

variable [IsOpenImmersion f] [IsOpenImmersion g]
  (hfg : Disjoint (Set.range f) (Set.range g))
include hfg

/-- The coproduct of two disjoint open charts makes no extra identifications. -/
theorem desc_injective : Function.Injective (coprod.desc f g) := by
  intro x y hxy
  rcases charts_cover x with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>
    rcases charts_cover y with ⟨b, rfl⟩ | ⟨b, rfl⟩
  · simp only [← Scheme.Hom.comp_apply, coprod.inl_desc] at hxy
    exact congrArg _ (f.isOpenEmbedding.injective hxy)
  · simp only [← Scheme.Hom.comp_apply, coprod.inl_desc, coprod.inr_desc] at hxy
    exact False.elim (Set.disjoint_left.mp hfg ⟨a, hxy⟩ ⟨b, rfl⟩)
  · simp only [← Scheme.Hom.comp_apply, coprod.inl_desc, coprod.inr_desc] at hxy
    exact False.elim (Set.disjoint_left.mp hfg ⟨b, rfl⟩ ⟨a, hxy⟩)
  · simp only [← Scheme.Hom.comp_apply, coprod.inr_desc] at hxy
    exact congrArg _ (g.isOpenEmbedding.injective hxy)

/-- Two disjoint open charts form one open immersion from their coproduct. -/
theorem desc_isOpenImmersion : IsOpenImmersion (coprod.desc f g) := by
  apply IsOpenImmersion.of_forall_source_exists _ (desc_injective f g hfg)
  intro x
  rcases charts_cover x with ⟨a, ha⟩ | ⟨b, hb⟩
  · refine ⟨_, coprod.inl, inferInstance, ⟨a, ha⟩, ?_⟩
    rw [coprod.inl_desc]
    infer_instance
  · refine ⟨_, coprod.inr, inferInstance, ⟨b, hb⟩, ?_⟩
    rw [coprod.inr_desc]
    infer_instance

end FLT.Mazur.SchemeDisjointOpenPair
