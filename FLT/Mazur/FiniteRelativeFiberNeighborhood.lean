/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeFiberMorphism
public import FLT.Mazur.ProperFiniteFiberNeighborhood

/-!
# A finite map on one base fiber spreads to a finite map

Finiteness of the actual induced fiber morphism gives finite point fibers
of the original map along that base fiber. This supplies the quasi-finite
locus argument without assuming any neighborhood finiteness.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.RelativeFiber

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (s : S)

/-- The original point fiber is the image of the point fiber of the induced morphism. -/
lemma image_preimage_singleton (x : (f ≫ g).fiber s) :
    (f ≫ g).fiberι s '' (map f g s ⁻¹' {map f g s x}) =
      f ⁻¹' {f ((f ≫ g).fiberι s x)} := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    change map f g s z = map f g s x at hz
    change f ((f ≫ g).fiberι s z) = f ((f ≫ g).fiberι s x)
    rw [← map_apply_ι, ← map_apply_ι, hz]
  · intro hy
    have hx : (f ≫ g) ((f ≫ g).fiberι s x) = s := ((f ≫ g).fiberHomeo s x).2
    have hy' : y ∈ Set.range ((f ≫ g).fiberι s) := by
      rw [Scheme.Hom.range_fiberι]
      change g (f y) = s
      change f y = f ((f ≫ g).fiberι s x) at hy
      rw [hy]
      exact hx
    obtain ⟨z, rfl⟩ := hy'
    refine ⟨z, ?_, rfl⟩
    change map f g s z = map f g s x
    apply (g.fiberι s).isEmbedding.injective
    rw [map_apply_ι, map_apply_ι]
    exact hy

/-- Finiteness of the induced morphism gives finite original point fibers along the base fiber. -/
lemma finite_preimage_singleton [IsFinite (map f g s)] (x : (f ≫ g).fiber s) :
    (f ⁻¹' {f ((f ≫ g).fiberι s x)}).Finite := by
  rw [← image_preimage_singleton f g s x]
  exact ((map f g s).finite_preimage_singleton _).image _

/-- A proper map finite on one whole base fiber is finite over a base neighborhood. -/
theorem exists_finite_neighborhood [IsProper (f ≫ g)] [IsSeparated g]
    [IsFinite (map f g s)] :
    ∃ V : S.Opens, s ∈ V ∧ IsFinite (f ∣_ (g ⁻¹ᵁ V)) := by
  let _ : IsProper f := IsProper.of_comp f g
  apply Approximation.exists_finite_over_base_neighborhood f g s
  intro x
  have : Finite (f.fiber (f ((f ≫ g).fiberι s x))) :=
    (f.fiberHomeo _).finite_iff.mpr (finite_preimage_singleton f g s x)
  exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _)

end FLT.Mazur.RelativeFiber
