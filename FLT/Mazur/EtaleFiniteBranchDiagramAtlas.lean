/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleFiniteBranchFiniteDiagram
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# A finite branch atlas carrying a prescribed finite diagram

Choose the constructed neighborhoods through every original source point.
They form a cover on the original relative fppf site. Every member has its
own finite etale coefficient cover and lifts all maps of the given diagram.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.EtaleFiniteBranchDiagramAtlas
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} {X Y A : Over S} [IsAffine A.left]
  (f : Y ⟶ A) [Etale f.left] (g₀ : X ⟶ Y) [Etale g₀.left]
  {ι : Type u} (s : Finset ι) (g : ι → (X ⟶ Y)) [∀ i, Etale (g i).left]

/-- Choose only the actual schemes and morphisms constructed by simultaneous refinement. -/
def data (x : X.left) : Σ (Z W : Over S), (W ⟶ A) × (Z ⟶ W) × (Z ⟶ X) :=
  let h := EtaleFiniteBranchDiagram.exists_finite_lifts f g₀ s g x
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose,
    h.choose_spec.choose_spec.choose_spec.choose,
    h.choose_spec.choose_spec.choose_spec.choose_spec.choose⟩

/-- The common affine source carrying all diagram arrows. -/
def source (x : X.left) : Over S := (data f g₀ s g x).1

/-- The affine coefficient neighborhood of the distinguished endpoint. -/
def target (x : X.left) : Over S := (data f g₀ s g x).2.1

/-- The coefficient map to the unchanged affine target. -/
def base (x : X.left) : target f g₀ s g x ⟶ A := (data f g₀ s g x).2.2.1

/-- The actual finite etale surjection on this common diagram neighborhood. -/
def projection (x : X.left) : source f g₀ s g x ⟶ target f g₀ s g x :=
  (data f g₀ s g x).2.2.2.1

/-- The etale map to the original source of the entire diagram. -/
def original (x : X.left) : source f g₀ s g x ⟶ X := (data f g₀ s g x).2.2.2.2

/-- The chosen data retain the geometry, point coverage, and every actual diagram lift. -/
theorem data_spec (x : X.left) :
    IsAffine (source f g₀ s g x).left ∧ IsAffine (target f g₀ s g x).left ∧
      Etale (base f g₀ s g x).left ∧ Etale (projection f g₀ s g x).left ∧
      IsFinite (projection f g₀ s g x).left ∧ Surjective (projection f g₀ s g x).left ∧
      Etale (original f g₀ s g x).left ∧
      original f g₀ s g x ≫ g₀ ≫ f = projection f g₀ s g x ≫ base f g₀ s g x ∧
      (∃ z : (source f g₀ s g x).left, (original f g₀ s g x).left z = x) ∧
      ∀ j ∈ s, ∃ (i : Y.left) (h : source f g₀ s g x ⟶ EtaleFiniteBranchAtlas.source f i),
        Etale h.left ∧ original f g₀ s g x ≫ g j =
          h ≫ EtaleFiniteBranchAtlas.original f i := by
  obtain ⟨z, hZ, hW, hb, ht, hf, hs, ha, he, hz, hl⟩ :=
    (EtaleFiniteBranchDiagram.exists_finite_lifts f g₀ s g x).choose_spec.choose_spec
      |>.choose_spec.choose_spec.choose_spec
  exact ⟨hZ, hW, hb, ht, hf, hs, ha, he, ⟨z, hz⟩, hl⟩

instance source_isAffine (x : X.left) : IsAffine (source f g₀ s g x).left :=
  (data_spec f g₀ s g x).1
instance target_isAffine (x : X.left) : IsAffine (target f g₀ s g x).left :=
  (data_spec f g₀ s g x).2.1
instance base_etale (x : X.left) : Etale (base f g₀ s g x).left :=
  (data_spec f g₀ s g x).2.2.1
instance projection_etale (x : X.left) : Etale (projection f g₀ s g x).left :=
  (data_spec f g₀ s g x).2.2.2.1
instance projection_isFinite (x : X.left) : IsFinite (projection f g₀ s g x).left :=
  (data_spec f g₀ s g x).2.2.2.2.1
instance projection_surjective (x : X.left) : Surjective (projection f g₀ s g x).left :=
  (data_spec f g₀ s g x).2.2.2.2.2.1
instance original_etale (x : X.left) : Etale (original f g₀ s g x).left :=
  (data_spec f g₀ s g x).2.2.2.2.2.2.1

/-- The distinguished original endpoint has exactly the constructed coefficient square. -/
@[reassoc]
theorem condition (x : X.left) :
    original f g₀ s g x ≫ g₀ ≫ f = projection f g₀ s g x ≫ base f g₀ s g x :=
  (data_spec f g₀ s g x).2.2.2.2.2.2.2.1

/-- Every original source point is covered. -/
theorem original_covers (x : X.left) :
    ∃ z : (source f g₀ s g x).left, (original f g₀ s g x).left z = x :=
  (data_spec f g₀ s g x).2.2.2.2.2.2.2.2.1

/-- Each member carries the whole prescribed finite diagram in the actual target branches. -/
theorem lifts (x : X.left) (j : ι) (hj : j ∈ s) :
    ∃ (i : Y.left) (h : source f g₀ s g x ⟶ EtaleFiniteBranchAtlas.source f i),
      Etale h.left ∧ original f g₀ s g x ≫ g j =
        h ≫ EtaleFiniteBranchAtlas.original f i :=
  (data_spec f g₀ s g x).2.2.2.2.2.2.2.2.2 j hj

/-- The constructed diagram neighborhoods form a full original fppf cover. -/
def fppfCover : Scheme.Cover.{u} Scheme.fppfPrecoverage X.left :=
  Scheme.Cover.mkOfCovers (P := @Flat ⊓ @LocallyOfFinitePresentation) X.left
    (fun x ↦ (source f g₀ s g x).left) (fun x ↦ (original f g₀ s g x).left)
    (fun x ↦ ⟨x, original_covers f g₀ s g x⟩) (fun _ ↦ ⟨inferInstance, inferInstance⟩)

/-- The covering sieve is on the unchanged relative fppf site. -/
theorem covering : Sieve.ofArrows (source f g₀ s g) (original f g₀ s g) ∈
    (Scheme.fppfTopology.over S) X := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact Precoverage.generate_mem_toGrothendieck (fppfCover f g₀ s g).mem₀

end FLT.Mazur.EtaleFiniteBranchDiagramAtlas
