/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicGeometricPointOrbit
public import FLT.Mazur.CyclicCharacteristicInvariantAffineCover

/-!
# The actual finite invariant affine cover is topologically saturated

Every arrow of the full same-chart comparison scheme preserves each original
invariant affine chart. This is a topological result, not a section-ring comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (i : InvariantAffineIndex n)

/-- Equivariance retains membership in the original affine chart in both directions. -/
theorem invariantAffineInclusion_range_action (e : RelabelGroup n)
    (x : normalizedLocus n i.1) :
    (normalizedRelabelAction n i.1 e).hom x ∈ Set.range (invariantAffineInclusion n i) ↔
      x ∈ Set.range (invariantAffineInclusion n i) := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨(invariantAffineAction n i e).inv y, ?_⟩
    apply (Scheme.homeoOfIso (normalizedRelabelAction n i.1 e)).injective
    have he := congrArg (fun k ↦ k ((invariantAffineAction n i e).inv y))
      (invariantAffineAction_inclusion n i e)
    have hi : (invariantAffineAction n i e).hom ((invariantAffineAction n i e).inv y) = y :=
      congrArg (fun k : invariantAffineChart n i ⟶ invariantAffineChart n i ↦ k y)
        (invariantAffineAction n i e).inv_hom_id
    change invariantAffineInclusion n i
      ((invariantAffineAction n i e).hom ((invariantAffineAction n i e).inv y)) =
        (normalizedRelabelAction n i.1 e).hom
          (invariantAffineInclusion n i ((invariantAffineAction n i e).inv y)) at he
    rw [hi] at he
    exact he.symm.trans hy
  · rintro ⟨y, rfl⟩
    exact ⟨(invariantAffineAction n i e).hom y,
      congrArg (fun k ↦ k y) (invariantAffineAction_inclusion n i e)⟩

/-- All actual same-chart arrows preserve the selected affine chart's underlying open. -/
theorem invariantAffineInclusion_range_saturated :
    productArrowSource n i.1 i.1 ⁻¹' Set.range (invariantAffineInclusion n i) =
      productArrowTarget n i.1 i.1 ⁻¹' Set.range (invariantAffineInclusion n i) := by
  ext x
  obtain ⟨e, he⟩ := productScheme_point_sameChart_orbit n i.1 x
  change productArrowSource n i.1 i.1 x ∈ Set.range (invariantAffineInclusion n i) ↔
    productArrowTarget n i.1 i.1 x ∈ Set.range (invariantAffineInclusion n i)
  rw [← he]
  exact (invariantAffineInclusion_range_action n i e _).symm

/-- Saturation holds as equality of actual opens on the full comparison scheme. -/
theorem invariantAffineInclusion_open_saturated :
    productArrowSource n i.1 i.1 ⁻¹ᵁ (invariantAffineInclusion n i).opensRange =
      productArrowTarget n i.1 i.1 ⁻¹ᵁ (invariantAffineInclusion n i).opensRange :=
  TopologicalSpace.Opens.ext (invariantAffineInclusion_range_saturated n i)

end FLT.Mazur.CyclicCharacteristicAtlas
