/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.SchemeOpenPushoutIntersection

/-!
# Replacing one open chart while retaining an arbitrary exterior

A modification that is unchanged over the full boundary induces a map of
open pushouts. Both old charts have exactly the expected inverse images.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.SchemeOpenReplacement
universe u
variable {O E B M : Scheme.{u}} (e : O ⟶ E) (b : O ⟶ B) (j : O ⟶ M)
  [IsOpenImmersion e] [IsOpenImmersion b] [IsOpenImmersion j]
  (f : M ⟶ B) (h : j ≫ f = b)

/-- Glue the actual modification map to the identity of the retained exterior. -/
def contraction : pushout e j ⟶ pushout e b :=
  pushout.desc (pushout.inl e b) (f ≫ pushout.inr e b) (by
    rw [← Category.assoc, h, pushout.condition])

@[reassoc (attr := simp)] theorem inl_contraction :
    pushout.inl e j ≫ contraction e b j f h = pushout.inl e b := pushout.inl_desc _ _ _

@[reassoc (attr := simp)] theorem inr_contraction :
    pushout.inr e j ≫ contraction e b j f h = f ≫ pushout.inr e b := pushout.inr_desc _ _ _

/-- No extra points appear over the retained exterior if the local boundary is complete. -/
theorem preimage_inl (hf : f ⁻¹' Set.range b = Set.range j) :
    (contraction e b j f h) ⁻¹' Set.range (pushout.inl e b) =
      Set.range (pushout.inl e j) := by
  apply Set.Subset.antisymm
  · intro z hz
    rcases SchemeOpenPushout.charts_cover e j z with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · exact ⟨a, rfl⟩
    · have ha : f a ∈ Set.range b := by
        rw [← SchemeOpenPushout.inr_preimage_inl e b]
        simpa only [Set.mem_preimage, ← Scheme.Hom.comp_apply, inr_contraction] using hz
      have ha' : a ∈ Set.range j := by rw [← hf]; exact ha
      obtain ⟨o, rfl⟩ := ha'
      exact ⟨e o, congrArg (fun g => g o) (pushout.condition (f := e) (g := j))⟩
  · rintro _ ⟨a, rfl⟩
    exact ⟨a, (congrArg (fun g => g a) (inl_contraction e b j f h)).symm⟩

/-- The inverse image of the replaced chart is the full local modification. -/
theorem preimage_inr :
    (contraction e b j f h) ⁻¹' Set.range (pushout.inr e b) =
      Set.range (pushout.inr e j) := by
  apply Set.Subset.antisymm
  · intro z hz
    rcases SchemeOpenPushout.charts_cover e j z with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · obtain ⟨c, hc⟩ := hz
      have hac : pushout.inl e b a = pushout.inr e b c := by
        simpa only [← Scheme.Hom.comp_apply, inl_contraction] using hc.symm
      obtain ⟨o, rfl, _⟩ := (SchemeOpenPushout.inl_eq_inr_iff e b a c).mp hac
      exact ⟨j o, (congrArg (fun g => g o) (pushout.condition (f := e) (g := j))).symm⟩
    · exact ⟨a, rfl⟩
  · rintro _ ⟨a, rfl⟩
    exact ⟨f a, (congrArg (fun g => g a) (inr_contraction e b j f h)).symm⟩

/-- The retained exterior square is cartesian over its entire open image. -/
theorem isPullback_inl (hf : f ⁻¹' Set.range b = Set.range j) :
    IsPullback (𝟙 E) (pushout.inl e j) (pushout.inl e b) (contraction e b j f h) := by
  apply IsOpenImmersion.isPullback _ _ _ _ (by simp)
  exact TopologicalSpace.Opens.ext (preimage_inl e b j f h hf)

/-- The local modification is the actual pullback over the old replaced chart. -/
theorem isPullback_inr :
    IsPullback f (pushout.inr e j) (pushout.inr e b) (contraction e b j f h) := by
  apply IsOpenImmersion.isPullback _ _ _ _ (by simp)
  exact TopologicalSpace.Opens.ext (preimage_inr e b j f h)

end FLT.Mazur.SchemeOpenReplacement
