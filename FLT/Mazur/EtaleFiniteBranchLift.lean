/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleFiniteBranchAtlas
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-!
# Finite branch neighborhoods compatible with an actual etale map

Pull back a chosen target branch along the original map, then construct a
finite branch through the resulting point. This retains an actual morphism
to the chosen target branch, rather than just a relation between point images.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.EtaleFiniteBranchLift
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} {X Y A : Over S} [IsAffine A.left]
  (f : Y ⟶ A) [Etale f.left] (g : X ⟶ Y) [Etale g.left]

/-- Every source point has a finite branch that maps into a selected target branch. -/
theorem exists_lift (x : X.left) :
    ∃ (i : Y.left) (Z W : Over S)
      (b : W ⟶ EtaleFiniteBranchAtlas.source f i) (t : Z ⟶ W) (a : Z ⟶ X)
      (z : Z.left), IsAffine Z.left ∧ IsAffine W.left ∧ Etale b.left ∧
      Etale t.left ∧ IsFinite t.left ∧ Surjective t.left ∧ Etale a.left ∧
      a ≫ g = t ≫ b ≫ EtaleFiniteBranchAtlas.original f i ∧ a.left z = x := by
  let i := g.left x
  let j := EtaleFiniteBranchAtlas.original f i
  let P := pullback g j
  let u : P ⟶ X := pullback.fst g j
  let v : P ⟶ EtaleFiniteBranchAtlas.source f i := pullback.snd g j
  have H := (IsPullback.of_hasPullback g j).map (Over.forget S)
  let _ : Etale u.left := MorphismProperty.of_isPullback H.flip
    (inferInstanceAs (Etale (EtaleFiniteBranchAtlas.original f i).left))
  let _ : Etale v.left := MorphismProperty.of_isPullback H (inferInstanceAs (Etale g.left))
  obtain ⟨y, hy⟩ := EtaleFiniteBranchAtlas.original_covers f i
  obtain ⟨r, hr, _⟩ := Scheme.exists_preimage_of_isPullback H x y hy.symm
  obtain ⟨Z, W, b, t, a, z, hZ, hW, hb, ht, hf, hs, ha, he, hz, _⟩ :=
    EtaleFiniteBranchNeighborhood.exists_cover v ⊤ r (by trivial)
  refine ⟨i, Z, W, b, t, a ≫ u, z, hZ, hW, hb, ht, hf, hs,
    inferInstanceAs (Etale (a.left ≫ u.left)), ?_, ?_⟩
  · calc
      (a ≫ u) ≫ g = a ≫ v ≫ j := by
        rw [Category.assoc, show u ≫ g = v ≫ j from pullback.condition]
      _ = t ≫ b ≫ j := by rw [← Category.assoc, he, Category.assoc]
  · change u.left (a.left z) = x
    rw [hz]
    exact hr

end FLT.Mazur.EtaleFiniteBranchLift
