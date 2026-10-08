/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeImageOpenCover
public import FLT.Mazur.IdealAdicRelativeTripleProjections

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

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y) (U V T : X.affineOpens)

attribute [local instance] relativeTensorChart_isOpenImmersion

/-- The structure morphism of the triple overlap into the changed-base scheme. -/
def relativeTripleToScheme : relativeTensorTripleOverlap J f U V T ⟶ relativeScheme J f :=
  relativeTripleFirstPairProjection J f U V T ≫ relativeOverlapToScheme J f U V

/-- The triple-overlap structure map is an open immersion. -/
instance relativeTripleToScheme_isOpenImmersion :
    IsOpenImmersion (relativeTripleToScheme J f U V T) := by
  unfold relativeTripleToScheme
  infer_instance

/-- The outer pair projection preserves the ambient structure map. -/
@[reassoc]
lemma relativeTripleOuterPairProjection_toScheme :
    relativeTripleOuterPairProjection J f U V T ≫ relativeOverlapToScheme J f U T =
      relativeTripleToScheme J f U V T := by
  rw [relativeOverlapToScheme, ← Category.assoc, relativeTripleOuterPairProjection_first]
  exact Category.assoc _ _ _

/-- The last pair projection preserves the ambient structure map. -/
@[reassoc]
lemma relativeTripleLastPairProjection_toScheme :
    relativeTripleLastPairProjection J f U V T ≫ relativeOverlapToScheme J f V T =
      relativeTripleToScheme J f U V T := by
  rw [relativeOverlapToScheme, ← Category.assoc, relativeTripleLastPairProjection_second,
    relativeTripleSecondThird_condition, ← relativeTripleFirstThird_condition]
  exact Category.assoc _ _ _

/-- The outer pair projection is an open immersion. -/
instance relativeTripleOuterPairProjection_isOpenImmersion :
    IsOpenImmersion (relativeTripleOuterPairProjection J f U V T) := by
  have : IsOpenImmersion (relativeTripleOuterPairProjection J f U V T ≫
      relativeOverlapToScheme J f U T) := by
    rw [relativeTripleOuterPairProjection_toScheme]
    infer_instance
  exact IsOpenImmersion.of_comp _ (relativeOverlapToScheme J f U T)

/-- The last pair projection is an open immersion. -/
instance relativeTripleLastPairProjection_isOpenImmersion :
    IsOpenImmersion (relativeTripleLastPairProjection J f U V T) := by
  have : IsOpenImmersion (relativeTripleLastPairProjection J f U V T ≫
      relativeOverlapToScheme J f V T) := by
    rw [relativeTripleLastPairProjection_toScheme]
    infer_instance
  exact IsOpenImmersion.of_comp _ (relativeOverlapToScheme J f V T)

/-- The triple-overlap image is the intersection of all three tensor image opens. -/
lemma relativeTripleToScheme_range :
    Set.range (relativeTripleToScheme J f U V T) =
      (relativeTensorImageOpen J f U ⊓ relativeTensorImageOpen J f V ⊓
        relativeTensorImageOpen J f T : (relativeScheme J f).Opens) := by
  have h := IsOpenImmersion.range_pullback_to_base_of_left
    (relativeOverlapToScheme J f U V) (relativeTensorChart J f T)
  change Set.range (relativeTripleToScheme J f U V T) = _ at h
  rw [relativeOverlapToScheme_range] at h
  exact h

/-- Identify the triple overlap with the actual triple intersection of image opens. -/
def relativeTripleImageIso : relativeTensorTripleOverlap J f U V T ≅
    (relativeTensorImageOpen J f U ⊓ relativeTensorImageOpen J f V ⊓
      relativeTensorImageOpen J f T).toScheme :=
  IsOpenImmersion.isoOfRangeEq (relativeTripleToScheme J f U V T)
    (relativeTensorImageOpen J f U ⊓ relativeTensorImageOpen J f V ⊓
      relativeTensorImageOpen J f T).ι
    (by rw [Scheme.Opens.range_ι]; exact relativeTripleToScheme_range J f U V T)

/-- The image identification preserves the ambient inclusion of the triple overlap. -/
@[reassoc]
lemma relativeTripleImageIso_hom_ι :
    (relativeTripleImageIso J f U V T).hom ≫
        (relativeTensorImageOpen J f U ⊓ relativeTensorImageOpen J f V ⊓
          relativeTensorImageOpen J f T).ι = relativeTripleToScheme J f U V T :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

end FLT.Mazur.IdealAdicGradedPullback
