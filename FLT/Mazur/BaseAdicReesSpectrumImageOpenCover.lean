/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesSpectrumTripleRefinement

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

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) (J : Ideal R)

attribute [local semireducible] modelSpectrum
attribute [local instance] spectrumSpaceMap_isOpenImmersion

/-- The image open of an original relative tensor chart. -/
def spectrumImageOpen (U : X.affineOpens) : (relativeSpace f J).Opens :=
  (spectrumSpaceMap f J U).opensRange

/-- The image opens cover the actual changed-base scheme. -/
lemma iSup_spectrumImageOpen : ⨆ U, spectrumImageOpen f J U = ⊤ := by
  apply top_le_iff.mp
  intro x _
  obtain ⟨U, z, hz⟩ := chartSpaceMap_covers f J x
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨U, z, hz⟩

/-- Identify the original tensor chart with its image open. -/
def spectrumImageIso (U : X.affineOpens) :
    modelSpectrum f J U ≅ (spectrumImageOpen f J U).toScheme :=
  (spectrumSpaceMap f J U).isoOpensRange

/-- The image identification retains the original tensor chart morphism. -/
@[reassoc]
lemma spectrumImageIso_hom_ι (U : X.affineOpens) :
    (spectrumImageIso f J U).hom ≫ (spectrumImageOpen f J U).ι =
      spectrumSpaceMap f J U := (spectrumSpaceMap f J U).isoOpensRange_hom_ι

/-- The inverse image identification also retains the tensor chart morphism. -/
@[reassoc]
lemma spectrumImageIso_inv_chart (U : X.affineOpens) :
    (spectrumImageIso f J U).inv ≫ spectrumSpaceMap f J U =
      (spectrumImageOpen f J U).ι := (spectrumSpaceMap f J U).isoOpensRange_inv_comp

/-- The structure map of the pair overlap into the changed-base scheme. -/
def spectrumOverlapToSpace (U V : X.affineOpens) :
    modelOverlap f J U V ⟶ relativeSpace f J :=
  spectrumOverlapFirst f J U V ≫ spectrumSpaceMap f J U

/-- The pair-overlap structure map is an open immersion. -/
instance spectrumOverlapToSpace_isOpenImmersion (U V : X.affineOpens) :
    IsOpenImmersion (spectrumOverlapToSpace f J U V) := by
  unfold spectrumOverlapToSpace spectrumOverlapFirst
  infer_instance

/-- The overlap image is exactly the intersection of the two chart images. -/
lemma spectrumOverlapToSpace_range (U V : X.affineOpens) :
    Set.range (spectrumOverlapToSpace f J U V) =
      (spectrumImageOpen f J U ⊓ spectrumImageOpen f J V :
        (relativeSpace f J).Opens) :=
  IsOpenImmersion.range_pullback_to_base_of_left
    (spectrumSpaceMap f J U) (spectrumSpaceMap f J V)

/-- Identify the pair overlap with the intersection of the two image opens. -/
def spectrumOverlapImageIso (U V : X.affineOpens) :
    modelOverlap f J U V ≅
      (spectrumImageOpen f J U ⊓ spectrumImageOpen f J V).toScheme :=
  IsOpenImmersion.isoOfRangeEq (spectrumOverlapToSpace f J U V)
    (spectrumImageOpen f J U ⊓ spectrumImageOpen f J V).ι
    (by rw [Scheme.Opens.range_ι]; exact spectrumOverlapToSpace_range f J U V)

/-- The pair image identification commutes with the ambient inclusion. -/
@[reassoc]
lemma spectrumOverlapImageIso_hom_ι (U V : X.affineOpens) :
    (spectrumOverlapImageIso f J U V).hom ≫
        (spectrumImageOpen f J U ⊓ spectrumImageOpen f J V).ι =
      spectrumOverlapToSpace f J U V := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The inverse pair image identification commutes with the ambient inclusion. -/
@[reassoc]
lemma spectrumOverlapImageIso_inv_toScheme (U V : X.affineOpens) :
    (spectrumOverlapImageIso f J U V).inv ≫ spectrumOverlapToSpace f J U V =
      (spectrumImageOpen f J U ⊓ spectrumImageOpen f J V).ι :=
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

end FLT.Mazur.BaseAdicRees
