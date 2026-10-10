/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXHorizontalScheme
public import FLT.Mazur.PrincipalAffineRefinement

/-!
# Full inverse image of the preceding horizontal boundary

The preceding horizontal coordinate pulls back to the retained coordinate
on the x-chart and to the scale times the deeper horizontal coordinate on
the divided chart. Thus every point over the old boundary is retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)

/-- On the x-chart the full inverse image is its retained principal open. -/
theorem horizontal_preimage_x :
    (toDivided W s π b3 b4 b6) ⁻¹'
        Set.range (previousHorizontalInclusion W s π b3 b4 b6) =
      Set.range (horizontalOpenInclusion W s π b3 b4 b6) := by
  change (PrimeSpectrum.comap (fromDivided W s π b3 b4 b6).toRingHom) ⁻¹'
    Set.range (PrincipalAffineRefinement.inclusion _) =
      Set.range (PrincipalAffineRefinement.inclusion _)
  rw [PrincipalAffineRefinement.range_inclusion, PrincipalAffineRefinement.range_inclusion]
  change (PrimeSpectrum.basicOpen (fromDivided W s π b3 b4 b6
    (WeierstrassDilatation.x W s (π * b3) (π * b4) (π ^ 2 * b6))) :
      Set (PrimeSpectrum (Coordinate W s π b3 b4 b6))) = _
  rw [fromDivided_x]

/-- A deeper divided point over the old boundary belongs to the actual gluing overlap. -/
theorem horizontal_preimage_divided_subset :
    (dividedToPrevious W s π b3 b4 b6) ⁻¹'
        Set.range (previousHorizontalInclusion W s π b3 b4 b6) ⊆
      Set.range (dividedOpenInclusion W s π b3 b4 b6) := by
  change (PrimeSpectrum.comap
    (WeierstrassDilatation.refinement W s π (π * b3) (π * b4) (π ^ 2 * b6)
      b3 b4 b6 rfl rfl rfl).toRingHom) ⁻¹'
    Set.range (PrincipalAffineRefinement.inclusion _) ⊆
      Set.range (PrincipalAffineRefinement.inclusion _)
  rw [PrincipalAffineRefinement.range_inclusion, PrincipalAffineRefinement.range_inclusion]
  intro z hz
  change WeierstrassDilatation.refinement W s π (π * b3) (π * b4) (π ^ 2 * b6)
    b3 b4 b6 rfl rfl rfl (WeierstrassDilatation.x W s (π * b3) (π * b4)
      (π ^ 2 * b6)) ∉ z.asIdeal at hz
  rw [WeierstrassDilatation.refinement_x] at hz
  exact fun hx => hz (z.asIdeal.mul_mem_left _ hx)

/-- The entire inverse image of the old boundary is the unchanged horizontal chart. -/
theorem horizontal_preimage :
    (contraction W s π b3 b4 b6) ⁻¹'
        Set.range (previousHorizontalInclusion W s π b3 b4 b6) =
      Set.range (previousHorizontalChart W s π b3 b4 b6) := by
  apply Set.Subset.antisymm
  · intro z hz
    have hx : ∀ a, xChart W s π b3 b4 b6 a = z →
        z ∈ Set.range (previousHorizontalChart W s π b3 b4 b6) := by
      intro a ha
      have ha' : a ∈ Set.range (horizontalOpenInclusion W s π b3 b4 b6) := by
        rw [← horizontal_preimage_x]
        simpa only [Set.mem_preimage, ← xChart_contraction, Scheme.Hom.comp_apply, ha] using hz
      obtain ⟨o, rfl⟩ := ha'
      refine ⟨(horizontalIso W s π b3 b4 b6).hom o, ?_⟩
      simpa only [previousHorizontalChart, ← Scheme.Hom.comp_apply,
        Iso.hom_inv_id_assoc] using ha
    rcases modification_charts_cover W s π b3 b4 b6 z with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact hx a ha
    · have ha' : a ∈ Set.range (dividedOpenInclusion W s π b3 b4 b6) := by
        apply horizontal_preimage_divided_subset W s π b3 b4 b6
        simpa only [Set.mem_preimage, ← dividedChart_contraction,
          Scheme.Hom.comp_apply, ha] using hz
      obtain ⟨o, rfl⟩ := ha'
      apply hx (xOpenInclusion W s π b3 b4 b6 ((overlapIso W s π b3 b4 b6).inv o))
      rw [← Scheme.Hom.comp_apply, chart_overlap]
      simpa only [overlapToDivided, ← Scheme.Hom.comp_apply,
        Category.assoc, Iso.inv_hom_id_assoc] using ha
  · rintro _ ⟨a, rfl⟩
    refine ⟨a, ?_⟩
    exact (congrArg (fun f => f a)
      (previousHorizontalChart_contraction W s π b3 b4 b6)).symm

end FLT.Mazur.WeierstrassSuccessiveX
