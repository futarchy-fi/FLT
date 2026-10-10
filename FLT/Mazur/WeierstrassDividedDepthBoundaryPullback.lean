/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDepthBoundary
public import FLT.Mazur.WeierstrassSuccessiveHorizontalPreimage

/-!
# The unchanged full boundary at each normalized depth

Transport the actual horizontal inverse image through the proved parameter
isomorphisms. The normalized local modification has no additional points
over the old boundary, and its square over that boundary is cartesian.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  {k : ℕ} (hπ : π ≠ 0) (d : Data W π k) (e : Data W π (k + 1))
open WeierstrassSuccessiveX

/-- The actual retained boundary of the normalized local modification. -/
def localBoundary : boundary d ⟶ depthStep π k W e.b3 e.b4 e.b6 :=
  previousToX hπ d e ≫ xChart W (π ^ k) π e.b3 e.b4 e.b6

instance localBoundary_isOpenImmersion : IsOpenImmersion (localBoundary hπ d e) := by
  unfold localBoundary
  infer_instance

/-- The actual normalized local contraction with its depth data bundled. -/
def localContraction : depthStep π k W e.b3 e.b4 e.b6 ⟶ chart d :=
  depthContraction π k hπ W d.b3 d.b4 d.b6 e.b3 e.b4 e.b6
    d.factor3 d.factor4 d.factor6 e.factor3 e.factor4 e.factor6

/-- The local contraction preserves all functions on the retained boundary. -/
@[reassoc] theorem localBoundary_contraction :
    localBoundary hπ d e ≫ localContraction hπ d e = boundaryInclusion d := by
  change previousToX hπ d e ≫ xChart W (π ^ k) π e.b3 e.b4 e.b6 ≫
    localContraction hπ d e = _
  change previousToX hπ d e ≫ xChart W (π ^ k) π e.b3 e.b4 e.b6 ≫
    contraction W (π ^ k) π e.b3 e.b4 e.b6 ≫ _ = _
  rw [xChart_contraction_assoc]
  exact previousToX_contraction hπ d e

/-- Over the complete preceding boundary, the normalized local step is the identity. -/
theorem localBoundary_isPullback :
    IsPullback (𝟙 (boundary d)) (localBoundary hπ d e)
      (boundaryInclusion d) (localContraction hπ d e) := by
  have H : IsPullback (𝟙 _) (previousHorizontalChart W (π ^ k) π e.b3 e.b4 e.b6)
      (previousHorizontalInclusion W (π ^ k) π e.b3 e.b4 e.b6)
      (contraction W (π ^ k) π e.b3 e.b4 e.b6) := by
    apply IsOpenImmersion.isPullback _ _ _ _
      (by simp only [Category.id_comp, previousHorizontalChart_contraction])
    exact TopologicalSpace.Opens.ext (horizontal_preimage W (π ^ k) π e.b3 e.b4 e.b6)
  apply H.of_iso (previousBoundaryIso hπ d e) (previousBoundaryIso hπ d e) (Iso.refl _)
    (WeierstrassDilatation.parameterSpecIso W (π ^ k) (π ^ k) d.b3 d.b4 d.b6
      (π * e.b3) (π * e.b4) (π ^ 2 * e.b6) rfl
      (factor3_step hπ d e) (factor4_step hπ d e) (factor6_step hπ d e))
  · simp
  · simp [localBoundary, previousToX, previousHorizontalChart]
  · exact (WeierstrassDilatation.horizontalParameterIso_inclusion W (π ^ k) (π ^ k)
      d.b3 d.b4 d.b6 (π * e.b3) (π * e.b4) (π ^ 2 * e.b6) rfl
      (factor3_step hπ d e) (factor4_step hπ d e) (factor6_step hπ d e)).symm
  · rfl

/-- The normalized local step has exactly the retained points over the old boundary. -/
theorem localBoundary_preimage :
    (localContraction hπ d e) ⁻¹' Set.range (boundaryInclusion d) =
      Set.range (localBoundary hπ d e) := by
  have H := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
    (localBoundary_isPullback hπ d e) ⊤
  simpa using (congrArg SetLike.coe H).symm

end FLT.Mazur.WeierstrassDividedDepth
