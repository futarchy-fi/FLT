/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSectionLinePoint

/-!
# Actual projective points on coordinate principal opens

The coordinate principal opens of a split vector cover the original affine
scheme. On each affine subopen where one coordinate is invertible, the
actual pulled-back vector constructs a projective point. These points
restrict correctly and agree when different coordinates are used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SplitLinePrincipalPoints
open NormalizedSectionLine ProjectiveSpace
variable {X : Scheme.{u}} [IsAffine X] {ι : Type u}
variable (v : ι → Γ(X, ⊤))

/-- A split vector's coordinate principal opens cover the original affine scheme. -/
lemma cover [Finite ι] (r : (ι → Γ(X, ⊤)) →ₗ[Γ(X, ⊤)] Γ(X, ⊤)) (hr : r v = 1) :
    (⨆ i, X.basicOpen (v i)) = ⊤ := by
  have h := (isAffineOpen_top X).iSup_basicOpen_eq_self_iff.mpr
    (generator_span_eq_top v r hr)
  simpa only [iSup_subtype, iSup_range] using h

/-- The defining coordinate is invertible on every smaller open. -/
lemma coordinate_isUnit (i : ι) (U : X.Opens) (hi : U ≤ X.basicOpen (v i)) :
    IsUnit (U.ι.appTop (v i)) := by
  have h : IsUnit ((X.basicOpen (v i)).ι.appTop (v i)) :=
    IsLocalization.Away.algebraMap_isUnit (v i)
  have h' := h.map (X.homOfLE hi).appTop.hom
  change IsUnit (((X.homOfLE hi) ≫ (X.basicOpen (v i)).ι).appTop (v i)) at h'
  simpa only [X.homOfLE_ι] using h'

/-- The actual coefficient vector on an affine subopen supplies its normalized image point. -/
def point (i : ι) (U : X.Opens) [IsAffine U.toScheme]
    (hi : U ≤ X.basicOpen (v i)) : U.toScheme ⟶ space Γ(X, ⊤) ι :=
  affineGeneratorPoint U.ι.appTop.hom (fun j ↦ U.ι.appTop (v j)) i
    (coordinate_isUnit v i U hi).unit (coordinate_isUnit v i U hi).unit_spec.symm

/-- Choice of an invertible coordinate does not change the original affine point. -/
lemma point_eq (i j : ι) (U : X.Opens) [IsAffine U.toScheme]
    (hi : U ≤ X.basicOpen (v i)) (hj : U ≤ X.basicOpen (v j)) :
    point v i U hi = point v j U hj := affineGeneratorPoint_eq _ _ _ _ _ _ _ _

omit [IsAffine X] in
/-- The scalar coefficients on nested opens are the original structural coefficients. -/
lemma scalars_comp {U V : X.Opens} (h : V ≤ U) :
    (X.homOfLE h).appTop.hom.comp U.ι.appTop.hom = V.ι.appTop.hom := by
  change ((X.homOfLE h) ≫ U.ι).appTop.hom = _
  rw [X.homOfLE_ι]

/-- Actual affine restriction preserves the constructed normalized projective point. -/
lemma point_restrict (i : ι) (U V : X.Opens) [IsAffine U.toScheme] [IsAffine V.toScheme]
    (hi : U ≤ X.basicOpen (v i)) (h : V ≤ U) :
    X.homOfLE h ≫ point v i U hi = point v i V (h.trans hi) := by
  rw [point, affineGeneratorPoint_pullback]
  have hc := scalars_comp h
  have hv : (fun j ↦ (X.homOfLE h).appTop (U.ι.appTop (v j))) =
      (fun j ↦ V.ι.appTop (v j)) := funext fun j ↦ DFunLike.congr_fun hc (v j)
  simp only [hc, hv, point, affineGeneratorPoint]
  apply (affineSectionLinePoint_eq_iff _ i i _ _).mpr
  rfl

end FLT.Mazur.SplitLinePrincipalPoints
