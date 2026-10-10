/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.SchemeOpenPushoutIntersection
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# An open two-chart cover is its actual pushout

When two open charts cover a scheme and their full intersection is given,
the resulting open pushout is isomorphic to the covered scheme.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.SchemeOpenPushout
universe u
variable {O E B Y : Scheme.{u}} (e : O ⟶ E) (b : O ⟶ B) (l : E ⟶ Y) (r : B ⟶ Y)
  [IsOpenImmersion e] [IsOpenImmersion b] [IsOpenImmersion l] [IsOpenImmersion r]
  (H : IsPullback e b l r)

include H in
omit [IsOpenImmersion r] in
/-- The full cartesian intersection accounts for any equal chart images. -/
theorem eq_of_cover_images (a : E) (c : B) (hac : l a = r c) :
    pushout.inl e b a = pushout.inr e b c := by
  have hrange : r ⁻¹' Set.range l = Set.range b := by
    have h := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H ⊤
    simpa using (congrArg SetLike.coe h).symm
  have hc : c ∈ Set.range b := by rw [← hrange]; exact ⟨a, hac⟩
  obtain ⟨o, rfl⟩ := hc
  have ho : e o = a := by
    apply l.isOpenEmbedding.injective
    exact (congrArg (fun g => g o) H.w).trans hac.symm
  exact (inl_eq_inr_iff e b a (b o)).mpr ⟨o, ho, rfl⟩

/-- Gluing the two chart inclusions introduces no extra identifications. -/
theorem coverDesc_injective : Function.Injective (pushout.desc l r H.w) := by
  intro x y hxy
  rcases charts_cover e b x with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>
    rcases charts_cover e b y with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · simp only [← Scheme.Hom.comp_apply, pushout.inl_desc] at hxy
    exact congrArg _ (l.isOpenEmbedding.injective hxy)
  · simp only [← Scheme.Hom.comp_apply, pushout.inl_desc, pushout.inr_desc] at hxy
    exact eq_of_cover_images e b l r H a c hxy
  · simp only [← Scheme.Hom.comp_apply, pushout.inl_desc, pushout.inr_desc] at hxy
    exact (eq_of_cover_images e b l r H c a hxy.symm).symm
  · simp only [← Scheme.Hom.comp_apply, pushout.inr_desc] at hxy
    exact congrArg _ (r.isOpenEmbedding.injective hxy)

/-- The comparison of the open pushout to the covered scheme is an open immersion. -/
theorem coverDesc_isOpenImmersion : IsOpenImmersion (pushout.desc l r H.w) := by
  apply IsOpenImmersion.of_forall_source_exists _ (coverDesc_injective e b l r H)
  intro x
  rcases charts_cover e b x with ⟨a, ha⟩ | ⟨a, ha⟩
  · refine ⟨_, pushout.inl e b, inferInstance, ⟨a, ha⟩, ?_⟩
    rw [pushout.inl_desc]
    infer_instance
  · refine ⟨_, pushout.inr e b, inferInstance, ⟨a, ha⟩, ?_⟩
    rw [pushout.inr_desc]
    infer_instance

/-- A full two-chart open cover is the actual pushout of its intersection. -/
def coverIso (hcover : ∀ y : Y, (∃ a, l a = y) ∨ ∃ c, r c = y) : pushout e b ≅ Y := by
  let _ := coverDesc_isOpenImmersion e b l r H
  have hiso : IsIso (pushout.desc l r H.w) := by
    apply isIso_of_isOpenImmersion_of_opensRange_eq_top
    apply TopologicalSpace.Opens.ext
    apply Set.range_eq_univ.mpr
    intro y
    rcases hcover y with ⟨a, ha⟩ | ⟨c, hc⟩
    · exact ⟨pushout.inl e b a, by
        simpa only [← Scheme.Hom.comp_apply, pushout.inl_desc] using ha⟩
    · exact ⟨pushout.inr e b c, by
        simpa only [← Scheme.Hom.comp_apply, pushout.inr_desc] using hc⟩
  exact asIso (pushout.desc l r H.w)

@[reassoc (attr := simp)] theorem inl_coverIso
    (hcover : ∀ y : Y, (∃ a, l a = y) ∨ ∃ c, r c = y) :
    pushout.inl e b ≫ (coverIso e b l r H hcover).hom = l := pushout.inl_desc _ _ _

@[reassoc (attr := simp)] theorem inr_coverIso
    (hcover : ∀ y : Y, (∃ a, l a = y) ∨ ∃ c, r c = y) :
    pushout.inr e b ≫ (coverIso e b l r H hcover).hom = r := pushout.inr_desc _ _ _

end FLT.Mazur.SchemeOpenPushout
