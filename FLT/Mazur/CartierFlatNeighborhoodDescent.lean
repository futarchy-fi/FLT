/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierFppfDescent

/-!
# Cartier neighborhoods descend from flat presented neighborhoods

A flat map locally of finite presentation is open. Restricting its target to
its open image makes it surjective, so fppf descent supplies actual Cartier
charts around every point of that image. No ideal presentation downstairs
is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X Y : Scheme.{u}}

/-- A Cartier pullback gives Cartier charts at every point reached by a flat presented map. -/
theorem cartierChart_of_flat_presented_neighborhood (I : Y.IdealSheafData) (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f] (hI : EffectiveCartier (I.comap f))
    (y : Y) (hy : y ∈ Set.range f) :
    ∃ U : Y.affineOpens, y ∈ U.1 ∧ CartierChart I U := by
  let W : Y.Opens := ⟨Set.range f, f.isOpenMap.isOpen_range⟩
  let g := pullback.snd f W.ι
  let _ : Surjective g := ⟨by
    intro z
    obtain ⟨x, hx⟩ := z.2
    obtain ⟨w, _, hw⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := W.ι) x z hx
    exact ⟨w, hw⟩⟩
  have hW : EffectiveCartier (I.comap W.ι) := by
    apply effectiveCartier_of_fppf_comap (I.comap W.ι) g
    have h := hI.comap_of_isOpenImmersion (pullback.fst f W.ι)
    rw [← Scheme.IdealSheafData.comap_comp, pullback.condition,
      Scheme.IdealSheafData.comap_comp] at h
    exact h
  obtain ⟨U, hyU, hU⟩ := hW ⟨y, hy⟩
  exact ⟨⟨W.ι ''ᵁ U, U.2.image_of_isOpenImmersion W.ι⟩,
    ⟨⟨y, hy⟩, hyU, rfl⟩, (cartierChart_comap_iff I W.ι U).mp hU⟩

end FLT.Mazur.FCurve
