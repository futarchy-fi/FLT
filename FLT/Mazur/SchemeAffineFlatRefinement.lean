/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import Mathlib.AlgebraicGeometry.Cover.Sigma
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Affine refinements retaining the original covering map

Over an affine target, a flat surjective open morphism has a finite affine
refinement. The finite coproduct is affine, and its map into the original
cover is flat and locally of finite presentation. The composite remains
faithfully flat. All maps are constructed from actual open subschemes.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeAffineDescent
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} [IsAffine X]

/-- A finite affine refinement of an open flat cover retains its map to the source. -/
theorem exists_affine_flat_refinement (p : Y ⟶ X) [Flat p] [Surjective p]
    (hp : IsOpenMap p) :
    ∃ (Z : Scheme.{u}) (_ : IsAffine Z) (b : Z ⟶ Y),
      Flat b ∧ LocallyOfFinitePresentation b ∧ Flat (b ≫ p) ∧ Surjective (b ≫ p) := by
  let C := p.cover (P := @Flat) inferInstance
  let : QuasiCompactCover C.toPreZeroHypercover :=
    .of_isOpenMap (fun _ ↦ hp)
  obtain ⟨D, k, hfin, hk⟩ := QuasiCompactCover.exists_hom C
  let : Finite D.cover.I₀ := hfin
  have (i : D.cover.I₀) : IsAffine (D.cover.X i) := inferInstanceAs (IsAffine (Spec _))
  let b : (∐ D.cover.X) ⟶ Y := Sigma.desc (fun i ↦ k.h₀ i)
  have hb : b ≫ p = Sigma.desc D.cover.f := by
    apply Sigma.hom_ext
    intro i
    simp only [b, Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
    exact k.w₀ i
  have hflat : Flat b := by
    apply IsZariskiLocalAtSource.sigmaDesc (P := @Flat)
    intro i
    have := hk i
    infer_instance
  have hfp : LocallyOfFinitePresentation b := by
    apply IsZariskiLocalAtSource.sigmaDesc (P := @LocallyOfFinitePresentation)
    intro i
    have := hk i
    infer_instance
  refine ⟨∐ D.cover.X, inferInstance, b, hflat, hfp, ?_, ?_⟩
  · rw [hb]
    exact D.cover.sigma.map_prop default
  · rw [hb]
    infer_instance

/-- Flat covers locally of finite presentation supply the required open refinement. -/
theorem exists_affine_fppf_refinement (p : Y ⟶ X)
    [Flat p] [Surjective p] [LocallyOfFinitePresentation p] :
    ∃ (Z : Scheme.{u}) (_ : IsAffine Z) (b : Z ⟶ Y),
      Flat b ∧ LocallyOfFinitePresentation b ∧ Flat (b ≫ p) ∧ Surjective (b ≫ p) :=
  exists_affine_flat_refinement p p.isOpenMap

end FLT.Mazur.SchemeAffineDescent
