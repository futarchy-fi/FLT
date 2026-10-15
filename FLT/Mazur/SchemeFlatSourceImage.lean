/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFppfTargetOpen

/-!
# Open images of original source opens over the whole-source flat locus

Restrict to the constructed flat target open before taking the image of a
source open. This image is genuinely open and retains the original target
scheme. Its points are exactly the original image points in the flat locus;
no global flatness or surjectivity hypothesis is introduced.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeFlatSourceImage
set_option backward.isDefEq.respectTransparency false
variable {A T : Scheme.{u}} (w : A ⟶ T) [LocallyOfFinitePresentation w] (U : A.Opens)
local notation "F" => SchemeFlatTargetOpen.locus w
local notation "a" => pullback.fst w (Scheme.Opens.ι (SchemeFlatTargetOpen.locus w))
local notation "b" => SchemeFppfTargetOpen.map w

/-- The open image is taken only after constructing the complete flat restriction. -/
def image : T.Opens :=
  ⟨b '' (a ⁻¹' (U : Set A)), (b).isOpenMap _ (U.isOpen.preimage (a).continuous)⟩

/-- Both the flat target condition and an actual original point are retained. -/
theorem mem_image_iff (y : T) : y ∈ image w U ↔
    y ∈ F ∧ ∃ x : A, x ∈ U ∧ w x = y := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(SchemeFlatTargetOpen.projection w z).property, a z, hz, ?_⟩
    exact congrArg (fun t ↦ t z) (pullback.condition (f := w) (g := (F).ι))
  · rintro ⟨hy, x, hx, hxy⟩
    obtain ⟨z, hz₁, hz₂⟩ := Scheme.exists_preimage_of_isPullback
      (IsPullback.of_hasPullback w (F).ι) x ⟨y, hy⟩ hxy
    refine ⟨z, ?_, ?_⟩
    · change a z ∈ U
      rwa [hz₁]
    · change (F).ι (pullback.snd w (F).ι z) = y
      rw [hz₂]
      rfl

/-- The image belongs to the maximal actual fppf region of the unchanged target. -/
theorem image_le_fppf : image w U ≤ SchemeFppfTargetOpen.locus w := by
  intro y hy
  obtain ⟨hf, x, _, hx⟩ := (mem_image_iff w U y).mp hy
  rw [← SetLike.mem_coe, SchemeFppfTargetOpen.coe_locus]
  exact ⟨⟨x, hx⟩, hf⟩

/-- Its complete original source projection is flat. -/
theorem projection_flat : Flat (pullback.snd w (image w U).ι) :=
  ((SchemeFppfTargetOpen.le_locus_iff w (image w U)).mp (image_le_fppf w U)).1

/-- Its complete original source projection is surjective. -/
theorem projection_surjective : Surjective (pullback.snd w (image w U).ι) :=
  ((SchemeFppfTargetOpen.le_locus_iff w (image w U)).mp (image_le_fppf w U)).2

/-- A source point survives when its target has a whole-source flat neighborhood. -/
theorem contains (x : A) (hx : x ∈ U) (hf : w x ∈ F) : w x ∈ image w U :=
  (mem_image_iff w U (w x)).mpr ⟨hf, x, hx, rfl⟩

/-- Fiberwise saturation prevents any extra original points from entering the retained source. -/
theorem preimage_le (hsat : ∀ x y : A, w x = w y → (x ∈ U ↔ y ∈ U)) :
    w ⁻¹ᵁ image w U ≤ U := by
  intro x hx
  obtain ⟨_, y, hy, he⟩ := (mem_image_iff w U (w x)).mp hx
  exact (hsat y x he).mp hy

end FLT.Mazur.SchemeFlatSourceImage
