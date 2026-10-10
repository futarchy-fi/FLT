/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativePrincipalCharts

/-!
# Common principal refinements of the actual relative charts

Membership in a relative chart is detected on the original ambient scheme.
Every point of a pairwise chart intersection lies in a chart which is
principal in both ambient affine opens.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

/-- An actual relative chart consists exactly of points lying over its ambient open. -/
lemma relativeTensorChart_mem_range_iff (U : X.affineOpens) (x : relativeScheme J f) :
    let := closedBaseAlgebra J f U.1
    x ∈ Set.range (relativeTensorChart J f U) ↔
      (J.comap f).subschemeι (relativeSchemeToClosed J f x) ∈ U.1 := by
  let := closedBaseAlgebra J f U.1
  constructor
  · rintro ⟨z, rfl⟩
    have he := congrArg (fun k ↦ k z) (relativeTensorChart_toClosed J f U)
    change relativeSchemeToClosed J f (relativeTensorChart J f U z) = _ at he
    rw [he]
    have hz : (closedAffineChart J f U).2.fromSpec (relativeTensorToChart J f U z) ∈
        Set.range (closedAffineChart J f U).2.fromSpec := ⟨_, rfl⟩
    rw [IsAffineOpen.range_fromSpec] at hz
    exact hz
  · intro hx
    have hz : relativeSchemeToClosed J f x ∈
        Set.range (closedAffineChart J f U).2.fromSpec := by
      rw [IsAffineOpen.range_fromSpec]
      exact hx
    obtain ⟨z, hz⟩ := hz
    obtain ⟨w, hw, _⟩ := Scheme.exists_preimage_of_isPullback
      (relativeTensorChart_isPullback J f U) x z hz.symm
    exact ⟨w, hw⟩

/-- Pairwise intersections of relative charts are covered by common principal refinements. -/
lemma relativeTensorChart_exists_common_principal (U V : X.affineOpens)
    (x : relativeScheme J f) :
    let := closedBaseAlgebra J f U.1
    let := closedBaseAlgebra J f V.1
    x ∈ Set.range (relativeTensorChart J f U) →
      x ∈ Set.range (relativeTensorChart J f V) →
      ∃ (r : Γ(X, U.1)) (s : Γ(X, V.1)),
        X.basicOpen r = X.basicOpen s ∧
        let W : X.affineOpens := ⟨X.basicOpen r, U.2.basicOpen r⟩
        let := closedBaseAlgebra J f W.1
        x ∈ Set.range (relativeTensorChart J f W) := by
  intro _ _ hxU hxV
  obtain ⟨r, s, hrs, hx⟩ := exists_basicOpen_le_affine_inter U.2 V.2
    ((J.comap f).subschemeι (relativeSchemeToClosed J f x))
    ⟨(relativeTensorChart_mem_range_iff J f U x).mp hxU,
      (relativeTensorChart_mem_range_iff J f V x).mp hxV⟩
  refine ⟨r, s, hrs, ?_⟩
  exact (relativeTensorChart_mem_range_iff J f ⟨X.basicOpen r, U.2.basicOpen r⟩ x).mpr hx

end FLT.Mazur.IdealAdicGradedPullback
