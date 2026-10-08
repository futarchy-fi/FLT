/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeOverlapProjections

/-!
# Image opens for relative tensor descent

The tensor charts give an open cover by their images. Their scheme-theoretic
pair overlaps identify canonically with the intersections of those images.
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

attribute [local instance] relativeTensorChart_isOpenImmersion

/-- The image open of an original relative tensor chart. -/
def relativeTensorImageOpen (U : X.affineOpens) : (relativeScheme J f).Opens :=
  (relativeTensorChart J f U).opensRange

/-- The image opens cover the actual changed-base scheme. -/
lemma iSup_relativeTensorImageOpen : ⨆ U, relativeTensorImageOpen J f U = ⊤ := by
  apply top_le_iff.mp
  intro x _
  obtain ⟨U, z, hz⟩ := relativeTensorChart_jointly_surjective J f x
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨U, z, hz⟩

/-- Identify the original tensor chart with its image open. -/
def relativeTensorImageIso (U : X.affineOpens) :
    Spec (.of (RelativeAlgebra J f U)) ≅ (relativeTensorImageOpen J f U).toScheme :=
  (relativeTensorChart J f U).isoOpensRange

/-- The image identification retains the original tensor chart morphism. -/
@[reassoc]
lemma relativeTensorImageIso_hom_ι (U : X.affineOpens) :
    (relativeTensorImageIso J f U).hom ≫ (relativeTensorImageOpen J f U).ι =
      relativeTensorChart J f U := (relativeTensorChart J f U).isoOpensRange_hom_ι

/-- The inverse image identification also retains the tensor chart morphism. -/
@[reassoc]
lemma relativeTensorImageIso_inv_chart (U : X.affineOpens) :
    (relativeTensorImageIso J f U).inv ≫ relativeTensorChart J f U =
      (relativeTensorImageOpen J f U).ι := (relativeTensorChart J f U).isoOpensRange_inv_comp

/-- The structure map of the pair overlap into the changed-base scheme. -/
def relativeOverlapToScheme (U V : X.affineOpens) :
    relativeTensorOverlap J f U V ⟶ relativeScheme J f :=
  relativeOverlapFirstProjection J f U V ≫ relativeTensorChart J f U

/-- The pair-overlap structure map is an open immersion. -/
instance relativeOverlapToScheme_isOpenImmersion (U V : X.affineOpens) :
    IsOpenImmersion (relativeOverlapToScheme J f U V) := by
  unfold relativeOverlapToScheme relativeOverlapFirstProjection
  infer_instance

/-- The overlap image is exactly the intersection of the two chart images. -/
lemma relativeOverlapToScheme_range (U V : X.affineOpens) :
    Set.range (relativeOverlapToScheme J f U V) =
      (relativeTensorImageOpen J f U ⊓ relativeTensorImageOpen J f V :
        (relativeScheme J f).Opens) :=
  IsOpenImmersion.range_pullback_to_base_of_left
    (relativeTensorChart J f U) (relativeTensorChart J f V)

/-- Identify the pair overlap with the intersection of the two image opens. -/
def relativeOverlapImageIso (U V : X.affineOpens) :
    relativeTensorOverlap J f U V ≅
      (relativeTensorImageOpen J f U ⊓ relativeTensorImageOpen J f V).toScheme :=
  IsOpenImmersion.isoOfRangeEq (relativeOverlapToScheme J f U V)
    (relativeTensorImageOpen J f U ⊓ relativeTensorImageOpen J f V).ι
    (by rw [Scheme.Opens.range_ι]; exact relativeOverlapToScheme_range J f U V)

/-- The pair image identification commutes with the ambient inclusion. -/
@[reassoc]
lemma relativeOverlapImageIso_hom_ι (U V : X.affineOpens) :
    (relativeOverlapImageIso J f U V).hom ≫
        (relativeTensorImageOpen J f U ⊓ relativeTensorImageOpen J f V).ι =
      relativeOverlapToScheme J f U V := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The inverse pair image identification commutes with the ambient inclusion. -/
@[reassoc]
lemma relativeOverlapImageIso_inv_toScheme (U V : X.affineOpens) :
    (relativeOverlapImageIso J f U V).inv ≫ relativeOverlapToScheme J f U V =
      (relativeTensorImageOpen J f U ⊓ relativeTensorImageOpen J f V).ι :=
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

end FLT.Mazur.IdealAdicGradedPullback
