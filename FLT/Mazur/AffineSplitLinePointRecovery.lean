/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSplitLineNormalizedSource
public import FLT.Mazur.SplitLineRestrictionSubobjects
public import FLT.Mazur.AffineSectionLineCanonicalPullback

/-!
# A framed affine reverse point determines its actual line subobject

The recovered vector supplies a principal cover. On each member a unit
coordinate identifies the original source with its normalized section line;
equality of points and subobject descent recover the original global inclusion.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.AffineSplitLineCoordinates
open FCurve AffineFreeSheafCoordinates NormalizedSectionLine ProjectiveSpace
variable {X : Scheme.{u}} [IsAffine X] {ι : Type u} [Finite ι] {L : X.Modules}
variable (e : L ≅ structureModule X) (s : L ⟶ SheafOfModules.free ι) [Mono s]
variable (r : SheafOfModules.free ι ⟶ L) (hr : s ≫ r = 𝟙 L)

/-- An affine framed inclusion with the given point is the original normalized subobject. -/
lemma subobject_eq_sectionLine (j : ι) (N : Chart Γ(X, ⊤) ι j)
    (hp : projectivePoint e s r hr = affineSectionLinePoint (.id _) j N) :
    Subobject.mk s = Subobject.mk (sectionLineInclusion X j N) := by
  apply ModuleSubobjectCoverEquality.subobject_eq_of_openCover s _
    (fun i ↦ X.basicOpen (vector e s i))
    (SplitLinePrincipalPoints.cover _ (retraction e r) (vector_retraction e s r hr))
  intro i
  let U := X.basicOpen (vector e s i)
  let f := U.ι
  let d := SplitSheafLinePullback.frame f e
  let t := SplitSheafLinePullback.inclusion f s
  let q := SplitSheafLinePullback.retraction f r
  have ht : t ≫ q = 𝟙 _ := SplitSheafLinePullback.inclusion_retraction f s r hr
  let _ : IsSplitMono t := IsSplitMono.mk' ⟨q, ht⟩
  have hu := SplitLinePrincipalPoints.coordinate_isUnit (vector e s) i U le_rfl
  have hv : vector d t i = hu.unit := by
    rw [vector_pullback]
    exact hu.unit_spec.symm
  apply SplitLineAffinePresentation.restriction_subobject_eq_of_pullback f s
  rw [canonicalSectionLinePullback_subobject]
  apply subobject_eq_sectionLine_of_unit d t q ht i hu.unit hv j
  apply (cancel_mono (coefficientMap f.appTop.hom ι)).mp
  rw [← projectivePoint_pullback f e s r hr, hp, affineSectionLinePoint_pullback,
    affineSectionLinePoint_coefficientMap, RingHom.id_comp, RingHom.comp_id]

end FLT.Mazur.AffineSplitLineCoordinates
