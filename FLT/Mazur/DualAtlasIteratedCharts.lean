/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DualAtlasAmbientBaseChange

/-!
# Original chart triples for successive geometric base changes

Compatible triples of original affine free charts cover the twice-pulled atlas.
Their composite base maps agree with the original chart map for the composite.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.DualAtlasIteratedCharts
open FCurve AffineFiniteFreeAtlas DualAtlasBaseChangeCharts
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)

/-- Three original affine free opens supporting both consecutive base changes. -/
structure Chart where
  /-- The original chart on the twice-pulled ambient sheaf. -/
  source : Index ((pullback f).obj ((pullback g).obj M))
  /-- The original chart on the intermediate ambient sheaf. -/
  middle : Index ((pullback g).obj M)
  /-- The original chart on the target ambient sheaf. -/
  target : Index M
  /-- The first map lands in the intermediate chart. -/
  first_le : source.val ≤ f ⁻¹ᵁ middle.val
  /-- The second map lands in the final chart. -/
  second_le : middle.val ≤ g ⁻¹ᵁ target.val

/-- The original supported pair for the first morphism. -/
def Chart.first (c : Chart f g M) : DualAtlasBaseChangeCharts.Chart f ((pullback g).obj M) :=
  ⟨c.source, c.middle, c.first_le⟩

/-- The original supported pair for the second morphism. -/
def Chart.second (c : Chart f g M) : DualAtlasBaseChangeCharts.Chart g M :=
  ⟨c.middle, c.target, c.second_le⟩

/-- The normalized source open and original target support the composite map. -/
def Chart.composite (c : Chart f g M) : DualAtlasBaseChangeCharts.Chart (f ≫ g) M where
  source := DualAtlasAmbient.index ((pullbackComp f g).app M) c.source
  target := c.target
  le_preimage _ hx := c.second_le (c.first_le hx)

/-- The consecutive affine base morphisms equal the original map for the composite. -/
lemma baseMap_comp (c : Chart f g M) :
    baseMap f ((pullback g).obj M) c.source c.middle c.first_le ≫
        baseMap g M c.middle c.target c.second_le =
      baseMap (f ≫ g) M (c.composite f g M).source c.target
        (c.composite f g M).le_preimage := by
  apply (cancel_mono c.target.val.ι).mp
  simp only [Category.assoc, baseMap_ι, baseMap_ι_assoc]
  rfl

variable (hM : LocallyFiniteFree M)
include hM in
/-- Compatible triples refine every neighborhood around every original base point. -/
lemma exists_chart {x : X} {U : X.Opens} (hx : x ∈ U) :
    ∃ c : Chart f g M, x ∈ c.source.val ∧ c.source.val ≤ U := by
  obtain ⟨d, hd, _⟩ := DualAtlasBaseChangeCharts.exists_chart g M hM
    (show f x ∈ (⊤ : Y.Opens) from trivial)
  obtain ⟨i, hi, hle⟩ := exists_mem_le ((pullback f).obj ((pullback g).obj M))
    ((hM.pullback g).pullback f) (show x ∈ U ⊓ f ⁻¹ᵁ d.source.val from ⟨hx, hd⟩)
  exact ⟨⟨i, d.source, d.target, hle.trans inf_le_right, d.le_preimage⟩,
    hi, hle.trans inf_le_left⟩

/-- Original projective charts supporting both geometric base changes cover the atlas. -/
def projectiveCover :
    (LocallyFreeDualProjectiveAtlas.space ((pullback f).obj ((pullback g).obj M))
      ((hM.pullback g).pullback f)).OpenCover where
  I₀ := Chart f g M
  X c := ProjectiveSpace.space Γ(c.source.val.toScheme, ⊤)
    (coordinates ((pullback f).obj ((pullback g).obj M)) c.source)
  f c := LocallyFreeDualProjectiveAtlas.chartMap _ _ c.source
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, inferInstance⟩
    obtain ⟨c, hc, _⟩ := exists_chart f g M hM
      (show LocallyFreeDualProjectiveAtlas.projection _ _ x ∈ (⊤ : X.Opens) from trivial)
    have hx : x ∈ LocallyFreeDualProjectiveAtlas.projection _ _ ⁻¹ᵁ c.source.val := hc
    rw [LocallyFreeDualProjectiveAtlas.projection_preimage] at hx
    exact ⟨c, hx⟩

end FLT.Mazur.DualAtlasIteratedCharts
