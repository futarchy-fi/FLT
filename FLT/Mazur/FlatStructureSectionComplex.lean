/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArtinianSectionKernel
public import FLT.Mazur.PolygonStructureInclusion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Flat terms of the actual structure-section complex

For a flat morphism to an affine base, the structure sections on each affine
open are flat over the original base functions. Thus a finite affine cover of
a separated source supplies the flat overlap term needed for Artinian lifting.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.FlatStructureSectionComplex
open Chow PolygonStructureInclusion
variable {X S : Scheme} (f : X ⟶ S)

/-- The scalar map on an affine open is the original affine-local structural map. -/
lemma restriction_scalar_eq (U : X.Opens) :
    (X.presheaf.map U.leTop.op).hom.comp f.appTop.hom =
      (f.appLE ⊤ U (by simp)).hom := by
  rfl

variable [IsAffine S] [Flat f]

/-- Structure sections on an affine open are flat with the original base action. -/
lemma affineSections_flat (U : X.Opens) (hU : IsAffineOpen U) :
    Module.Flat Γ(S, ⊤) (baseSections (structureModule X) f.appTop.hom U) := by
  have h := f.flat_appLE (isAffineOpen_top S) hU (by simp)
  rw [← restriction_scalar_eq f U] at h
  exact h

/-- A finite affine cover has a flat product of chart sections. -/
lemma chartProduct_flat {ι : Type} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) :
    Module.Flat Γ(S, ⊤) (∀ i, baseSections (structureModule X) f.appTop.hom (U i)) := by
  classical
  let _ := Fintype.ofFinite ι
  let _ (i : ι) := affineSections_flat f (U i) (hU i)
  exact Module.Flat.of_linearEquiv (DFinsupp.linearEquivFunOnFintype
    (R := Γ(S, ⊤)) (M := fun i ↦ baseSections (structureModule X) f.appTop.hom (U i))).symm

/-- Affine intersections provide the flat final term of the actual two-term complex. -/
lemma overlapProduct_flat [X.IsSeparated] {ι : Type} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) :
    Module.Flat Γ(S, ⊤)
      (∀ ij : ι × ι, baseSections (structureModule X) f.appTop.hom (U ij.1 ⊓ U ij.2)) :=
  chartProduct_flat f _ (fun ij ↦ (hU ij.1).inf (hU ij.2))

end FLT.Mazur.FlatStructureSectionComplex
