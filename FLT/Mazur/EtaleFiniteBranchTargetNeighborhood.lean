/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleFiniteBranchNeighborhood

/-!
# Finite etale branches with independently prescribed source and target neighborhoods

The target need not be affine. First select an actual affine target open, then
construct a finite etale branch inside the prescribed source open. The result
retains the original relative morphism and both neighborhood conditions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.EtaleFiniteBranchTargetNeighborhood
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) [Etale f.left]

/-- Construct finite covers in both prescribed opens without assuming an affine target. -/
theorem exists_cover (Ω : X.left.Opens) (Ψ : Y.left.Opens)
    (x : X.left) (hx : x ∈ Ω) (hy : f.left x ∈ Ψ) :
    ∃ (Z W : Over S) (b : W ⟶ Y) (t : Z ⟶ W) (a : Z ⟶ X) (z : Z.left),
      IsAffine Z.left ∧ IsAffine W.left ∧ Etale b.left ∧ Etale t.left ∧
        IsFinite t.left ∧ Surjective t.left ∧ Etale a.left ∧
        a ≫ f = t ≫ b ∧ a.left z = x ∧
        Set.range a.left ⊆ Ω ∧ Set.range b.left ⊆ Ψ := by
  obtain ⟨U, hU, hxU, hUΨ⟩ := exists_isAffineOpen_mem_and_subset hy
  let Y' : Over S := Over.mk (U.ι ≫ Y.hom)
  let X' : Over S := Over.mk ((f.left ⁻¹ᵁ U).ι ≫ X.hom)
  let i : Y' ⟶ Y := Over.homMk U.ι
  let j : X' ⟶ X := Over.homMk (f.left ⁻¹ᵁ U).ι
  let g : X' ⟶ Y' := Over.homMk (f.left ∣_ U) (by
    change (f.left ∣_ U) ≫ (U.ι ≫ Y.hom) = (f.left ⁻¹ᵁ U).ι ≫ X.hom
    rw [morphismRestrict_ι_assoc, f.w])
  let _ : IsAffine Y'.left := hU
  let _ : Etale g.left := inferInstanceAs (Etale (f.left ∣_ U))
  have hg : g ≫ i = j ≫ f := Over.OverMorphism.ext (morphismRestrict_ι f.left U)
  obtain ⟨Z, W, b, t, a, z, hZ, hW, hb, ht, hf, hs, ha, he, hz, hΩ⟩ :=
    EtaleFiniteBranchNeighborhood.exists_cover g (j.left ⁻¹ᵁ Ω) ⟨x, hxU⟩ hx
  refine ⟨Z, W, b ≫ i, t, a ≫ j, z, hZ, hW,
    inferInstanceAs (Etale (b.left ≫ U.ι)), ht, hf, hs,
    inferInstanceAs (Etale (a.left ≫ (f.left ⁻¹ᵁ U).ι)), ?_, ?_, ?_, ?_⟩
  · rw [Category.assoc, ← hg, ← Category.assoc, he, Category.assoc]
  · exact congrArg Subtype.val hz
  · rintro _ ⟨y, rfl⟩
    exact hΩ ⟨y, rfl⟩
  · rintro _ ⟨y, rfl⟩
    exact hUΨ (b.left y).property

end FLT.Mazur.EtaleFiniteBranchTargetNeighborhood
