/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeEtaleFiniteBranchCover

/-!
# Finite etale branches inside prescribed original neighborhoods

An arbitrary etale scheme over an affine target has finite etale branch
covers through every point, inside every prescribed open. Both constructed
schemes are affine, and all morphisms retain the original relative base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.EtaleFiniteBranchNeighborhood
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} {X Y : Over S} [IsAffine Y.left]
  (f : X ⟶ Y) [Etale f.left]

/-- Finite etale branch covers can be constructed inside any original open neighborhood. -/
theorem exists_cover (Ω : X.left.Opens) (x : X.left) (hx : x ∈ Ω) :
    ∃ (Z W : Over S) (b : W ⟶ Y) (t : Z ⟶ W) (a : Z ⟶ X) (z : Z.left),
      IsAffine Z.left ∧ IsAffine W.left ∧ Etale b.left ∧ Etale t.left ∧
        IsFinite t.left ∧ Surjective t.left ∧ Etale a.left ∧
        a ≫ f = t ≫ b ∧ a.left z = x ∧ Set.range a.left ⊆ Ω := by
  obtain ⟨U, hU, hxU, hUΩ⟩ := exists_isAffineOpen_mem_and_subset hx
  let U' : Over S := Over.mk (U.ι ≫ X.hom)
  let j : U' ⟶ X := Over.homMk U.ι
  let _ : IsAffine U'.left := hU
  let _ : Etale (j ≫ f).left := inferInstanceAs (Etale (U.ι ≫ f.left))
  obtain ⟨Z, W, b, t, a, z, hZ, hW, hb, ht, hf, hs, ha, heq, hz⟩ :=
    RelativeEtaleFiniteBranchCover.exists_cover (j ≫ f) ⟨x, hxU⟩
  refine ⟨Z, W, b, t, a ≫ j, z, hZ, hW, hb, ht, hf, hs,
    inferInstanceAs (Etale (a.left ≫ U.ι)), ?_, ?_, ?_⟩
  · simpa only [Category.assoc] using heq
  · exact congrArg Subtype.val hz
  · rintro _ ⟨y, rfl⟩
    exact hUΩ (a.left y).property

end FLT.Mazur.EtaleFiniteBranchNeighborhood
