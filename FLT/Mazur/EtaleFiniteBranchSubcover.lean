/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleFiniteBranchAtlas
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Finitely many actual branches covering a quasi-compact étale source

Compactness selects finitely many members of the constructed branch atlas.
Their sources, finite étale projections, coefficient neighborhoods, and original
scheme maps are unchanged. They still jointly cover the entire source.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.EtaleFiniteBranchAtlas
universe u
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} {X Y : Over S} [IsAffine Y.left]
  (f : X ⟶ Y) [Etale f.left] [CompactSpace X.left]

/-- A finite set of original branch labels still covers every point of the source. -/
theorem exists_finite_cover : ∃ t : Finset X.left,
    ∀ x : X.left, ∃ r ∈ t, ∃ z : (source f r).left, (original f r).left z = x := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun r ↦ Set.range (original f r).left)
    (fun r ↦ (original f r).left.isOpenMap.isOpen_range)
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, original_covers f x⟩)
  refine ⟨t, fun x ↦ ?_⟩
  obtain ⟨r, hr, z, hz⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  exact ⟨r, hr, z, hz⟩

/-- Actual finitely many labels, selected from the original full branch atlas. -/
def finiteLabels : Finset X.left := (exists_finite_cover f).choose

/-- Every original point is covered by a selected original branch. -/
theorem finiteLabels_covers (x : X.left) :
    ∃ r : finiteLabels f, ∃ z : (source f r.val).left, (original f r.val).left z = x := by
  obtain ⟨r, hr, z, hz⟩ := (exists_finite_cover f).choose_spec x
  exact ⟨⟨r, hr⟩, z, hz⟩

/-- A finite étale covering family on the whole original source. -/
def finiteCover : Scheme.Cover.{u} Scheme.etalePrecoverage X.left :=
  Scheme.Cover.mkOfCovers (P := @Etale) (finiteLabels f)
    (fun r : finiteLabels f ↦ (source f r.val).left)
    (fun r ↦ (original f r.val).left) (finiteLabels_covers f) (fun _ ↦ inferInstance)

instance : Finite (finiteCover f).I₀ := inferInstanceAs (Finite (finiteLabels f))

/-- The same selected maps form a finite fppf covering family. -/
def finiteFppfCover : Scheme.Cover.{u} Scheme.fppfPrecoverage X.left :=
  Scheme.Cover.mkOfCovers (P := @Flat ⊓ @LocallyOfFinitePresentation) (finiteLabels f)
    (fun r : finiteLabels f ↦ (source f r.val).left)
    (fun r ↦ (original f r.val).left) (finiteLabels_covers f)
    (fun _ ↦ ⟨inferInstance, inferInstance⟩)

instance : Finite (finiteFppfCover f).I₀ := inferInstanceAs (Finite (finiteLabels f))

/-- Each selected source remains affine. -/
instance finiteFppfCover_isAffine (r : (finiteFppfCover f).I₀) :
    IsAffine ((finiteFppfCover f).X r) := inferInstanceAs (IsAffine (source f r.val).left)

end FLT.Mazur.EtaleFiniteBranchAtlas
