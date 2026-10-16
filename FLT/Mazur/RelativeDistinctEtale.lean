/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeDistinctTuples
public import FLT.Mazur.EtaleMarkingScheme

/-!
# Etale ordered-point schemes and their clopen tuple inclusion

For an etale source, each collision equation is open as well as closed.
The constructed distinct-point locus is therefore clopen and is affine
whenever the full relative tuple scheme is affine.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme} (E : Over S) [Etale E.hom] (I : Type) [Fintype I]

/-- The full original tuple scheme is etale over its unchanged base. -/
instance tuples_etale : Etale (tuples E I).hom := EtaleMarkingScheme.product_etale _

/-- Every actual coordinate collision is an open immersion for an etale source. -/
instance collisionInclusion_open (i j : I) :
    IsOpenImmersion (collisionInclusion E I i j).left :=
  EtaleMarkingScheme.equalizer_open _ _

/-- The equality locus is open, including its original scheme structure. -/
theorem collisionLocus_isOpen (i j : I) : IsOpen (collisionLocus E I i j) :=
  (collisionInclusion E I i j).left.isOpenEmbedding.isOpen_range

variable [IsSeparated E.hom]

/-- The distinct-point open has closed underlying set; no component was selected. -/
theorem distinctOpen_isClosed : IsClosed (distinctOpen E I : Set (tuples E I).left) :=
  isClosed_iInter fun a ↦ (collisionLocus_isOpen E I a.val.1 a.val.2).isClosed_compl

/-- Ordered distinct points of the entire etale scheme form an etale scheme. -/
instance distinctScheme_etale : Etale (distinctScheme E I).hom := by
  change Etale ((distinctOpen E I).ι ≫ (tuples E I).hom)
  infer_instance

/-- The clopen tuple inclusion is affine, without finite-fiber or rank hypotheses. -/
instance distinctInclusion_affine : IsAffineHom (distinctInclusion E I).left := by
  apply isAffineHom_of_isInducing
  · exact (distinctOpen E I).ι.isOpenEmbedding.isInducing
  · change IsClosed (Set.range (distinctOpen E I).ι)
    rw [Scheme.Opens.range_ι]
    exact distinctOpen_isClosed E I

/-- An affine full tuple scheme gives an actual affine ordered-point scheme. -/
instance distinctScheme_affine [IsAffine (tuples E I).left] :
    IsAffine (distinctScheme E I).left :=
  isAffine_of_isAffineHom (distinctInclusion E I).left

end FLT.Mazur.RelativeOrderedTuples
