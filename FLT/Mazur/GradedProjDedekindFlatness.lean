/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedProjStructuralMap
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Flatness of Proj over a Dedekind coefficient ring

The degree-zero homogeneous localizations embed in localizations of the
original flat algebra. They are torsion-free over the original scalars, hence
flat. The standard affine cover then proves flatness of the structural map.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

namespace FLT.Mazur.GradedProjDedekindFlatness

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [IsDedekindDomain R] [Module.Flat R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

/-- The chart's specified structural scalar map is flat. -/
theorem scalarToAway_flat (f : A) : (GradedProjStructuralMap.scalarToAway 𝒜 f).Flat := by
  let _ : Algebra R (Away 𝒜 f) := (GradedProjStructuralMap.scalarToAway 𝒜 f).toAlgebra
  let _ : Module.IsTorsionFree R (Away 𝒜 f) :=
    Function.Injective.moduleIsTorsionFree
      (HomogeneousLocalization.val (𝒜 := 𝒜) (x := .powers f)) (val_injective _) (by
        intro r s
        rw [Algebra.smul_def, val_mul, Algebra.smul_def]
        congr 1)
  change Module.Flat R (Away 𝒜 f)
  infer_instance

/-- A positive-degree standard affine chart is flat over the original scalar spectrum. -/
theorem away_toBase_flat {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    Flat (Proj.awayι 𝒜 f hf hd ≫ GradedProjStructuralMap.toSpecBase 𝒜) := by
  rw [GradedProjStructuralMap.awayι_toSpecBase, Flat.SpecMap_iff]
  exact scalarToAway_flat 𝒜 f

/-- Proj of the flat graded algebra is flat over its original Dedekind coefficient ring. -/
theorem toSpecBase_flat : Flat (GradedProjStructuralMap.toSpecBase 𝒜) := by
  apply (IsZariskiLocalAtSource.iff_of_openCover (Proj.affineOpenCover 𝒜).openCover).mpr
  intro i
  exact away_toBase_flat 𝒜 i.2.property i.1.property

end FLT.Mazur.GradedProjDedekindFlatness
