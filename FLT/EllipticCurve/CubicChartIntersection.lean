/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicChartPoint

/-! # The coordinate overlap is the actual intersection of the glued charts -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem affineChart_preimage_infinityChart :
    affineChart W ⁻¹ᵁ (infinityChart W).opensRange = (overlapInclusion W false).opensRange := by
  ext x
  change (∃ y, infinityChart W y = affineChart W x) ↔
    ∃ z, overlapInclusion W false z = x
  constructor
  · rintro ⟨y, hy⟩
    have h : colimit.ι (span (overlapInclusion W false) (overlapRight W)) WalkingSpan.left x =
        colimit.ι (span (overlapInclusion W false) (overlapRight W)) WalkingSpan.right y :=
      hy.symm
    obtain ⟨k, ki, kj, z, hx, _⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff
        (span (overlapInclusion W false) (overlapRight W))).mp h
    cases k with
    | none =>
      cases ki
      cases kj
      exact ⟨z, hx⟩
    | some k =>
      cases k with
      | left => cases kj
      | right => cases ki
  · rintro ⟨z, rfl⟩
    exact ⟨overlapRight W z, (congrArg (fun f ↦ f z) (overlap_condition W)).symm⟩

/-- The explicit coordinate overlap realizes the categorical intersection of the charts. -/
theorem chart_overlap_isPullback :
    IsPullback (overlapInclusion W false) (overlapRight W)
      (affineChart W) (infinityChart W) :=
  (IsOpenImmersion.isPullback (overlapRight W) (overlapInclusion W false)
    (infinityChart W) (affineChart W) (overlap_condition W)
    (affineChart_preimage_infinityChart W)).flip


/-- The same intersection, expressed in the infinity chart's overlap coordinates. -/
theorem chart_overlap_true_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (changeChart W true).toRingHom))
      (overlapInclusion W true) (affineChart W) (infinityChart W) := by
  apply (chart_overlap_isPullback W).of_iso (overlapIso W)
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id]
    apply (cancel_mono (affineChart W)).mp
    rw [Category.assoc, changeChart_true_to_scheme, ← Category.assoc]
    exact overlap_condition W
  · simp only [Iso.refl_hom, Category.comp_id]
    rfl
  · simp
  · simp

end WeierstrassCurve.CubicCharts
