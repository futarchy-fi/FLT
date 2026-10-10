/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DualAtlasBaseChangeCharts

/-!
# A cover by original charts admitting geometric base-change maps

Pairs of original source and target affine free charts, with the source in
the target's inverse image, cover both the new base and its projective atlas.
The resulting local maps therefore suffice for geometric descent.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.DualAtlasBaseChangeCharts
open FCurve AffineFiniteFreeAtlas
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)

/-- Original source and target charts on which the base morphism factors. -/
structure Chart where
  /-- An original affine free chart of the pulled ambient sheaf. -/
  source : Index ((pullback f).obj M)
  /-- An original affine free chart of the target ambient sheaf. -/
  target : Index M
  /-- The original base morphism maps the source chart into the target chart. -/
  le_preimage : source.val ≤ f ⁻¹ᵁ target.val

variable (hM : LocallyFiniteFree M)

include hM in
/-- These pairs refine every source neighborhood around every point. -/
lemma exists_chart {x : X} {U : X.Opens} (hx : x ∈ U) :
    ∃ c : Chart f M, x ∈ c.source.val ∧ c.source.val ≤ U := by
  obtain ⟨j, hj, _⟩ := exists_mem_le M hM
    (show f x ∈ (⊤ : Y.Opens) from trivial)
  obtain ⟨i, hi, hle⟩ := exists_mem_le ((pullback f).obj M) (hM.pullback f)
    (show x ∈ U ⊓ f ⁻¹ᵁ j.val from ⟨hx, hj⟩)
  exact ⟨⟨i, j, hle.trans inf_le_right⟩, hi, hle.trans inf_le_left⟩

/-- The original source opens supporting the constructed maps cover the new base. -/
def baseCover : X.OpenCover where
  I₀ := Chart f M
  X c := c.source.val.toScheme
  f c := c.source.val.ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, inferInstance⟩
    obtain ⟨c, hc, _⟩ := exists_chart f M hM (show x ∈ (⊤ : X.Opens) from trivial)
    exact ⟨c, ⟨⟨x, hc⟩, rfl⟩⟩

/-- The corresponding original projective charts cover the actual pulled ambient atlas. -/
def projectiveCover :
    (LocallyFreeDualProjectiveAtlas.space ((pullback f).obj M) (hM.pullback f)).OpenCover where
  I₀ := Chart f M
  X c := ProjectiveSpace.space Γ(c.source.val.toScheme, ⊤)
    (coordinates ((pullback f).obj M) c.source)
  f c := LocallyFreeDualProjectiveAtlas.chartMap ((pullback f).obj M) (hM.pullback f) c.source
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, inferInstance⟩
    obtain ⟨c, hc, _⟩ := exists_chart f M hM
      (show LocallyFreeDualProjectiveAtlas.projection ((pullback f).obj M)
        (hM.pullback f) x ∈ (⊤ : X.Opens) from trivial)
    have hx : x ∈ LocallyFreeDualProjectiveAtlas.projection ((pullback f).obj M)
        (hM.pullback f) ⁻¹ᵁ c.source.val := hc
    rw [LocallyFreeDualProjectiveAtlas.projection_preimage] at hx
    exact ⟨c, hx⟩

/-- Equality of morphisms on the constructed original projective charts is global equality. -/
lemma hom_ext {Z : Scheme.{u}}
    (a b : LocallyFreeDualProjectiveAtlas.space ((pullback f).obj M) (hM.pullback f) ⟶ Z)
    (h : ∀ c : Chart f M,
      LocallyFreeDualProjectiveAtlas.chartMap ((pullback f).obj M) (hM.pullback f) c.source ≫ a =
        LocallyFreeDualProjectiveAtlas.chartMap ((pullback f).obj M)
          (hM.pullback f) c.source ≫ b) : a = b :=
  (projectiveCover f M hM).hom_ext a b h

end FLT.Mazur.DualAtlasBaseChangeCharts
