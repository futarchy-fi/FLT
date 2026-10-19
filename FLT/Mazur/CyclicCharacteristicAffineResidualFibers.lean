/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineResidualSections

/-!
# Exact full residual fibers on the affine refinement

Equality of affine-source quotient points is witnessed by the actual restricted
comparison scheme. In particular the full residual invariant spectrum map is
constant on these quotient fibers, without deleting any scheme arrows.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (i : InvariantAffineIndex n)

/-- Equal quotient points in one affine chart have an actual full restricted comparison arrow. -/
theorem affineOrbitProjection_eq_iff (x y : invariantAffineChart n i) :
    affineOrbitProjection n i x = affineOrbitProjection n i y ↔
      ∃ a : (affineResidualDomain n i).toScheme,
        affineResidualSource n i a = x ∧ affineResidualTarget n i a = y := by
  constructor
  · intro h
    obtain ⟨a, ha, ht⟩ := (chartProjection_eq_iff n i.1 i.1
      (invariantAffineInclusion n i x) (invariantAffineInclusion n i y)).mp
        (congrArg Subtype.val h)
    have hm : a ∈ affineResidualDomain n i := by
      change productArrowSource n i.1 i.1 a ∈ Set.range (invariantAffineInclusion n i)
      exact ⟨x, ha.symm⟩
    refine ⟨⟨a, hm⟩, ?_, ?_⟩
    · apply (invariantAffineInclusion n i).isOpenEmbedding.injective
      exact (congrArg (fun f => f ⟨a, hm⟩) (affineResidualSource_inclusion n i)).trans ha
    · apply (invariantAffineInclusion n i).isOpenEmbedding.injective
      exact (congrArg (fun f => f ⟨a, hm⟩) (affineResidualTarget_inclusion n i)).trans ht
  · rintro ⟨a, rfl, rfl⟩
    apply Subtype.ext
    change chartProjection n i.1 (invariantAffineInclusion n i (affineResidualSource n i a)) =
      chartProjection n i.1 (invariantAffineInclusion n i (affineResidualTarget n i a))
    have hs := congrArg (fun f => f a) (affineResidualSource_inclusion n i)
    have ht := congrArg (fun f => f a) (affineResidualTarget_inclusion n i)
    change invariantAffineInclusion n i (affineResidualSource n i a) =
      productArrowSource n i.1 i.1 a.val at hs
    change invariantAffineInclusion n i (affineResidualTarget n i a) =
      productArrowTarget n i.1 i.1 a.val at ht
    rw [hs, ht]
    exact (chartProjection_eq_iff n i.1 i.1 _ _).mpr ⟨a.val, rfl, rfl⟩

/-- The full residual spectrum projection is constant on actual quotient fibers. -/
theorem affineResidualProjection_eq_of_orbit_eq {x y : invariantAffineChart n i}
    (h : affineOrbitProjection n i x = affineOrbitProjection n i y) :
    affineResidualProjection n i x = affineResidualProjection n i y := by
  obtain ⟨a, rfl, rfl⟩ := (affineOrbitProjection_eq_iff n i x y).mp h
  exact congrArg (fun f => f a)
    (SchemeRelationInvariantSpectrum.projection_condition
      (affineResidualSource n i) (affineResidualTarget n i))

end FLT.Mazur.CyclicCharacteristicOrbit
