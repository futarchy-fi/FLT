/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeImageOpenCover

/-!
# The opens used by the relative affine pushforward

The inverse image of each original affine open is exactly its tensor-chart
image. Thus pushforward sections on that open can be computed on one chart.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

/-- The affine projection to the original source, including the closed immersion. -/
def relativeSchemeToSource : relativeScheme J f ⟶ X :=
  relativeSchemeToClosed J f ≫ (J.comap f).subschemeι

instance relativeSchemeToSource_isAffineHom : IsAffineHom (relativeSchemeToSource J f) :=
  inferInstanceAs (IsAffineHom (relativeSchemeToClosed J f ≫ (J.comap f).subschemeι))

/-- The Cartesian tensor chart is exactly the inverse image of the closed affine chart. -/
lemma relativeTensorImageOpen_eq_preimage (U : X.affineOpens) :
    relativeTensorImageOpen J f U =
      relativeSchemeToClosed J f ⁻¹ᵁ (closedAffineChart J f U).1 := by
  let := closedBaseAlgebra J f U.1
  apply TopologicalSpace.Opens.ext
  ext x
  change (∃ z, relativeTensorChart J f U z = x) ↔ _
  constructor
  · rintro ⟨z, rfl⟩
    have h := congrArg (fun k ↦ k z) (relativeTensorChart_toClosed J f U)
    change relativeSchemeToClosed J f (relativeTensorChart J f U z) ∈
      (closedAffineChart J f U).1
    simp only [Scheme.Hom.comp_apply] at h
    rw [h]
    exact (IsAffineOpen.range_fromSpec (closedAffineChart J f U).2).le
      ⟨relativeTensorToChart J f U z, rfl⟩
  · intro hx
    obtain ⟨z, hz⟩ := (IsAffineOpen.range_fromSpec
      (closedAffineChart J f U).2).ge hx
    obtain ⟨w, hw, _⟩ := Scheme.exists_preimage_of_isPullback
      (relativeTensorChart_isPullback J f U) x z hz.symm
    exact ⟨w, hw⟩

/-- Inverse images of the original affine opens are the tensor-chart image opens. -/
lemma relativeSchemeToSource_preimage (U : X.affineOpens) :
    relativeSchemeToSource J f ⁻¹ᵁ U.1 = relativeTensorImageOpen J f U := by
  rw [relativeTensorImageOpen_eq_preimage]
  rfl

/-- Original affine inclusions induce inclusions of the chart images. -/
lemma relativeTensorImageOpen_mono {U V : X.affineOpens} (i : U.1 ⟶ V.1) :
    relativeTensorImageOpen J f U ≤ relativeTensorImageOpen J f V := by
  rw [← relativeSchemeToSource_preimage, ← relativeSchemeToSource_preimage]
  exact fun _ hx ↦ (leOfHom i) hx

end FLT.Mazur.IdealAdicGradedPullback
