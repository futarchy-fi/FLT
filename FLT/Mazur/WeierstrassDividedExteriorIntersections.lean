/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedExteriorStep
public import FLT.Mazur.SchemeOpenPushoutIntersection

/-!
# Exact intersections with a new successive chart

Both boundaries of a new successive chart are the full intersections with
the preceding exterior and the deeper divided chart. These are cartesian
squares of actual schemes, before any coefficient extension.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  {k : ℕ} (hπ : π ≠ 0) {d : Data W π k} (E : Exterior d) (e : Data W π (k + 1))

/-- The entire previous boundary is the intersection in the enlarged exterior. -/
theorem Exterior.newX_retained_preimage :
    E.newX hπ e ⁻¹' Set.range (E.retained hπ e) = Set.range (previousToX hπ d e) :=
  SchemeOpenPushout.inr_preimage_inl E.attach (previousToX hπ d e)

/-- The preceding exterior attachment is a full cartesian intersection. -/
theorem Exterior.retained_newX_isPullback :
    IsPullback E.attach (previousToX hπ d e) (E.retained hπ e) (E.newX hπ e) :=
  SchemeOpenPushout.isPullback E.attach (previousToX hπ d e)

/-- The complete next boundary is the preimage of the divided chart in the new chart. -/
theorem Exterior.newX_divided_preimage :
    (E.newX hπ e ≫ (E.advance hπ e).exteriorChart) ⁻¹'
      Set.range (E.advance hπ e).dividedChart = Set.range (nextToX e) := by
  ext z
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨o, ho, _⟩ := (SchemeOpenPushout.inl_eq_inr_iff
      (E.advance hπ e).attach (boundaryInclusion e) (E.newX hπ e z) y).mp hy.symm
    exact ⟨o, (E.newX hπ e).isOpenEmbedding.injective ho⟩
  · rintro ⟨o, rfl⟩
    exact ⟨boundaryInclusion e o,
      (congrArg (fun f => f o) (Exterior.overlap (E.advance hπ e))).symm⟩

/-- The deeper divided attachment is exactly the fiber product of the full charts. -/
theorem Exterior.newX_divided_isPullback :
    IsPullback (nextToX e) (boundaryInclusion e)
      (E.newX hπ e ≫ (E.advance hπ e).exteriorChart)
      (E.advance hπ e).dividedChart := by
  apply IsPullback.flip
  apply IsOpenImmersion.isPullback
    (boundaryInclusion e) (nextToX e) (E.advance hπ e).dividedChart
    (E.newX hπ e ≫ (E.advance hπ e).exteriorChart)
  · exact (Category.assoc _ _ _).symm.trans (Exterior.overlap (E.advance hπ e))
  · exact TopologicalSpace.Opens.ext (E.newX_divided_preimage hπ e)

end FLT.Mazur.WeierstrassDividedDepth
