/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleFiniteBranchLift

/-!
# Simultaneous refinement of finite diagrams by actual finite branches

Every finite family of etale maps has a common affine etale neighborhood
on which all maps factor through constructed branches of the target atlas.
The equalities are equalities of relative scheme morphisms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.EtaleFiniteBranchDiagram
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} {Y A : Over S} [IsAffine A.left]
  (f : Y ⟶ A) [Etale f.left]

/-- All maps in a finite diagram lift simultaneously to the constructed branch atlas. -/
theorem exists_lifts {ι : Type u} (s : Finset ι) {X : Over S}
    (g : ι → (X ⟶ Y)) [∀ i, Etale (g i).left] (x : X.left) :
    ∃ (Z : Over S) (a : Z ⟶ X) (z : Z.left),
      IsAffine Z.left ∧ Etale a.left ∧ a.left z = x ∧
      ∀ j ∈ s, ∃ (i : Y.left) (h : Z ⟶ EtaleFiniteBranchAtlas.source f i),
        Etale h.left ∧ a ≫ g j = h ≫ EtaleFiniteBranchAtlas.original f i := by
  classical
  induction s using Finset.induction_on generalizing X with
  | empty =>
    obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ (⊤ : X.left.Opens) from trivial)
    let Z : Over S := Over.mk (U.ι ≫ X.hom)
    let a : Z ⟶ X := Over.homMk U.ι
    exact ⟨Z, a, ⟨x, hxU⟩, hU, inferInstanceAs (Etale U.ι), rfl,
      fun _ h ↦ (Finset.notMem_empty _ h).elim⟩
  | @insert j s hj ih =>
    obtain ⟨i, Z, W, b, t, a, z, hZ, hW, hb, ht, hf, hs, ha, he, hz⟩ :=
      EtaleFiniteBranchLift.exists_lift f (g j) x
    let g' : ι → (Z ⟶ Y) := fun l ↦ a ≫ g l
    let _ (l : ι) : Etale (g' l).left := inferInstanceAs (Etale (a.left ≫ (g l).left))
    obtain ⟨T, v, w, hT, hv, hw, hl⟩ := ih g' z
    refine ⟨T, v ≫ a, w, hT, inferInstanceAs (Etale (v.left ≫ a.left)), ?_, ?_⟩
    · change a.left (v.left w) = x
      rw [hw, hz]
    · intro l hl'
      rcases Finset.mem_insert.mp hl' with rfl | hls
      · refine ⟨i, v ≫ t ≫ b,
          inferInstanceAs (Etale (v.left ≫ t.left ≫ b.left)), ?_⟩
        rw [Category.assoc, he]
        simp only [Category.assoc]
      · obtain ⟨i', h, hh, he'⟩ := hl l hls
        exact ⟨i', h, hh, (Category.assoc _ _ _).trans he'⟩

end FLT.Mazur.EtaleFiniteBranchDiagram
