/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleFiniteBranchDiagram

/-!
# Finite etale covers carrying a whole finite branch diagram

After simultaneously lifting the diagram, take one more constructed finite
branch. The common source is now finite etale surjective over an affine
coefficient neighborhood, while all original diagram factorizations survive.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.EtaleFiniteBranchDiagram
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} {X Y A : Over S} [IsAffine A.left]
  (f : Y ⟶ A) [Etale f.left] (g₀ : X ⟶ Y) [Etale g₀.left]

/-- A finite etale coefficient cover can carry every map of the finite diagram. -/
theorem exists_finite_lifts {ι : Type u} (s : Finset ι)
    (g : ι → (X ⟶ Y)) [∀ i, Etale (g i).left] (x : X.left) :
    ∃ (Z W : Over S) (b : W ⟶ A) (t : Z ⟶ W) (a : Z ⟶ X) (z : Z.left),
      IsAffine Z.left ∧ IsAffine W.left ∧ Etale b.left ∧
      Etale t.left ∧ IsFinite t.left ∧ Surjective t.left ∧ Etale a.left ∧
      a ≫ g₀ ≫ f = t ≫ b ∧ a.left z = x ∧
      ∀ j ∈ s, ∃ (i : Y.left) (h : Z ⟶ EtaleFiniteBranchAtlas.source f i),
        Etale h.left ∧ a ≫ g j = h ≫ EtaleFiniteBranchAtlas.original f i := by
  obtain ⟨T, v, w, hT, hv, hw, hl⟩ := exists_lifts f s g x
  let _ : Etale (v ≫ g₀).left := inferInstanceAs (Etale (v.left ≫ g₀.left))
  obtain ⟨i, Z, W, b, t, a, z, hZ, hW, hb, ht, hf, hs, ha, he, hz⟩ :=
    EtaleFiniteBranchLift.exists_lift f (v ≫ g₀) w
  let b' : W ⟶ A := b ≫ EtaleFiniteBranchAtlas.original f i ≫ f
  let _ : Etale b'.left := inferInstanceAs
    (Etale (b.left ≫ (EtaleFiniteBranchAtlas.original f i).left ≫ f.left))
  refine ⟨Z, W, b', t, a ≫ v, z, hZ, hW, inferInstance, ht, hf, hs,
    inferInstanceAs (Etale (a.left ≫ v.left)), ?_, ?_, ?_⟩
  · calc
      (a ≫ v) ≫ g₀ ≫ f = (a ≫ (v ≫ g₀)) ≫ f := by simp only [Category.assoc]
      _ = t ≫ b' := by rw [he]; simp only [b', Category.assoc]
  · change v.left (a.left z) = x
    rw [hz, hw]
  · intro j hj
    obtain ⟨i', h, hh, he'⟩ := hl j hj
    refine ⟨i', a ≫ h, inferInstanceAs (Etale (a.left ≫ h.left)), ?_⟩
    rw [Category.assoc, he', Category.assoc]

end FLT.Mazur.EtaleFiniteBranchDiagram
