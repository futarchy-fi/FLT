/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesSpectrumImageOpenCover
public import FLT.Mazur.BaseAdicReesSpectrumTripleProjections

/-!
# The image of the relative triple overlap

The full triple intersection identifies with the intersection of the three
image opens, compatibly with its maps to each pair overlap.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) (J : Ideal R)
  (U V T : X.affineOpens)

attribute [local semireducible] modelSpectrum
attribute [local instance] spectrumSpaceMap_isOpenImmersion

/-- The structure morphism of the triple overlap into the changed-base scheme. -/
def spectrumTripleToScheme : spectrumTripleOverlap f J U V T ⟶ relativeSpace f J :=
  spectrumTripleFirstPairProjection f J U V T ≫ spectrumOverlapToSpace f J U V

/-- The triple-overlap structure map is an open immersion. -/
instance spectrumTripleToScheme_isOpenImmersion :
    IsOpenImmersion (spectrumTripleToScheme f J U V T) := by
  unfold spectrumTripleToScheme
  infer_instance

/-- The outer pair projection preserves the ambient structure map. -/
@[reassoc]
lemma spectrumTripleOuterPairProjection_toScheme :
    spectrumTripleOuterPairProjection f J U V T ≫ spectrumOverlapToSpace f J U T =
      spectrumTripleToScheme f J U V T := by
  rw [spectrumOverlapToSpace, ← Category.assoc, spectrumTripleOuterPairProjection_first]
  exact Category.assoc _ _ _

/-- The last pair projection preserves the ambient structure map. -/
@[reassoc]
lemma spectrumTripleLastPairProjection_toScheme :
    spectrumTripleLastPairProjection f J U V T ≫ spectrumOverlapToSpace f J V T =
      spectrumTripleToScheme f J U V T := by
  rw [spectrumOverlapToSpace, ← Category.assoc, spectrumTripleLastPairProjection_second,
    spectrumTripleSecondThird_condition, ← spectrumTripleFirstThird_condition]
  exact Category.assoc _ _ _

/-- The outer pair projection is an open immersion. -/
instance spectrumTripleOuterPairProjection_isOpenImmersion :
    IsOpenImmersion (spectrumTripleOuterPairProjection f J U V T) := by
  have : IsOpenImmersion (spectrumTripleOuterPairProjection f J U V T ≫
      spectrumOverlapToSpace f J U T) := by
    rw [spectrumTripleOuterPairProjection_toScheme]
    infer_instance
  exact IsOpenImmersion.of_comp _ (spectrumOverlapToSpace f J U T)

/-- The last pair projection is an open immersion. -/
instance spectrumTripleLastPairProjection_isOpenImmersion :
    IsOpenImmersion (spectrumTripleLastPairProjection f J U V T) := by
  have : IsOpenImmersion (spectrumTripleLastPairProjection f J U V T ≫
      spectrumOverlapToSpace f J V T) := by
    rw [spectrumTripleLastPairProjection_toScheme]
    infer_instance
  exact IsOpenImmersion.of_comp _ (spectrumOverlapToSpace f J V T)

/-- The triple-overlap image is the intersection of all three tensor image opens. -/
lemma spectrumTripleToScheme_range :
    Set.range (spectrumTripleToScheme f J U V T) =
      (spectrumImageOpen f J U ⊓ spectrumImageOpen f J V ⊓
        spectrumImageOpen f J T : (relativeSpace f J).Opens) := by
  have h := IsOpenImmersion.range_pullback_to_base_of_left
    (spectrumOverlapToSpace f J U V) (spectrumSpaceMap f J T)
  change Set.range (spectrumTripleToScheme f J U V T) = _ at h
  rw [spectrumOverlapToSpace_range] at h
  exact h

/-- Identify the triple overlap with the actual triple intersection of image opens. -/
def spectrumTripleImageIso : spectrumTripleOverlap f J U V T ≅
    (spectrumImageOpen f J U ⊓ spectrumImageOpen f J V ⊓
      spectrumImageOpen f J T).toScheme :=
  IsOpenImmersion.isoOfRangeEq (spectrumTripleToScheme f J U V T)
    (spectrumImageOpen f J U ⊓ spectrumImageOpen f J V ⊓
      spectrumImageOpen f J T).ι
    (by rw [Scheme.Opens.range_ι]; exact spectrumTripleToScheme_range f J U V T)

/-- The image identification preserves the ambient inclusion of the triple overlap. -/
@[reassoc]
lemma spectrumTripleImageIso_hom_ι :
    (spectrumTripleImageIso f J U V T).hom ≫
        (spectrumImageOpen f J U ⊓ spectrumImageOpen f J V ⊓
          spectrumImageOpen f J T).ι = spectrumTripleToScheme f J U V T :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

end FLT.Mazur.BaseAdicRees
