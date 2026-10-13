/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineEtaleFiniteBranch
public import FLT.Mazur.FiniteEtaleImageCover

/-!
# Relative finite etale branch covers through original points

The constructed branch covers its coefficient image by a finite etale
surjection. All maps are over the unchanged base scheme. The other arrow
is an etale neighborhood of the prescribed original point.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.RelativeEtaleFiniteBranchCover
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} {X Y : Over S} [IsAffine X.left] [IsAffine Y.left]
  (f : X ⟶ Y) [Etale f.left]

/-- An actual finite etale relative cover, with an etale map through the selected source point. -/
theorem exists_cover (x : X.left) :
    ∃ (Z W : Over S) (b : W ⟶ Y) (t : Z ⟶ W) (a : Z ⟶ X) (z : Z.left),
      IsAffine Z.left ∧ IsAffine W.left ∧ Etale b.left ∧ Etale t.left ∧ IsFinite t.left ∧
        Surjective t.left ∧ Etale a.left ∧ a ≫ f = t ≫ b ∧ a.left z = x := by
  obtain ⟨Z, W, b, t, a, z, hZ, hW, hb, ht, hfin, ha, hsq, hz, _⟩ :=
    AffineEtaleFiniteBranch.exists_branch f.left x
  let W' : Over S := Over.mk ((FiniteEtaleImageCover.imageOpen t).ι ≫ b ≫ Y.hom)
  let Z' : Over S := Over.mk (a ≫ X.hom)
  let b' : W' ⟶ Y := Over.homMk ((FiniteEtaleImageCover.imageOpen t).ι ≫ b)
    (Category.assoc _ _ _)
  let a' : Z' ⟶ X := Over.homMk a
  have hbase : FiniteEtaleImageCover.cover t ≫ W'.hom = Z'.hom := by
    dsimp only [W', Z', Over.mk_hom]
    rw [FiniteEtaleImageCover.cover_ι_assoc, ← Category.assoc, ← hsq,
      Category.assoc, f.w]
  let t' : Z' ⟶ W' := Over.homMk (FiniteEtaleImageCover.cover t) hbase
  refine ⟨Z', W', b', t', a', z, hZ,
    inferInstanceAs (IsAffine (FiniteEtaleImageCover.imageOpen t)),
    inferInstanceAs (Etale ((FiniteEtaleImageCover.imageOpen t).ι ≫ b)),
    inferInstanceAs (Etale (FiniteEtaleImageCover.cover t)),
    inferInstanceAs (IsFinite (FiniteEtaleImageCover.cover t)),
    inferInstanceAs (Surjective (FiniteEtaleImageCover.cover t)), ha, ?_, hz⟩
  apply Over.OverMorphism.ext
  change a ≫ f.left = FiniteEtaleImageCover.cover t ≫
    ((FiniteEtaleImageCover.imageOpen t).ι ≫ b)
  rw [FiniteEtaleImageCover.cover_ι_assoc]
  exact hsq

end FLT.Mazur.RelativeEtaleFiniteBranchCover
