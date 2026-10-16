/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeCompleteFrameComparison
public import FLT.Mazur.RelativeDistinctSubframe

/-!
# Every distinct frame is a unique subframe of a complete frame

Only the larger frame must enumerate the whole geometric fiber. The other finite
label type is independent, and its frame may be incomplete.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  {I J : Type} [Fintype I] [Fintype J] {K : Type} [Field K] {b : Spec (.of K) ⟶ S}
  (a : Over.mk b ⟶ distinctScheme E I)
  (ha : Function.Bijective (fun i ↦ geometricCoordinate E I a i default))
  (a' : Over.mk b ⟶ distinctScheme E J)

/-- Embed every label of an arbitrary frame into the complete original frame. -/
def completeSubframeEmbedding : J ↪ I where
  toFun j := (completeCoordinateEquiv E I a ha).symm (a' ≫ distinctCoordinate E J j)
  inj' := by
    let _ : Nonempty (Over.mk b).left := inferInstanceAs (Nonempty (Spec (.of K)))
    exact (completeCoordinateEquiv E I a ha).symm.injective.comp
      (distinctCoordinate_injective E J a')

/-- The embedding matches whole original coordinate morphisms. -/
theorem completeSubframeEmbedding_coordinate (j : J) :
    a ≫ distinctCoordinate E I (completeSubframeEmbedding E a ha a' j) =
      a' ≫ distinctCoordinate E J j :=
  (completeCoordinateEquiv E I a ha).apply_symm_apply _

/-- The arbitrary geometric frame is the selected subframe as an actual scheme test. -/
theorem completeSubframeEmbedding_factor :
    a ≫ subframe E (completeSubframeEmbedding E a ha a') = a' := by
  apply distinct_hom_ext E J
  intro j
  rw [Category.assoc, subframe_coordinate]
  exact completeSubframeEmbedding_coordinate E a ha a' j

/-- No other injection selects this original frame from the complete one. -/
theorem completeSubframeEmbedding_unique (ι : J ↪ I)
    (h : a ≫ subframe E ι = a') : ι = completeSubframeEmbedding E a ha a' := by
  let _ : Nonempty (Over.mk b).left := inferInstanceAs (Nonempty (Spec (.of K)))
  ext j
  apply distinctCoordinate_injective E I a
  change a ≫ distinctCoordinate E I (ι j) =
    a ≫ distinctCoordinate E I (completeSubframeEmbedding E a ha a' j)
  rw [completeSubframeEmbedding_coordinate]
  have hj := congrArg (fun f ↦ f ≫ distinctCoordinate E J j) h
  simpa only [Category.assoc, subframe_coordinate] using hj

include ha a' in
/-- An arbitrary distinct frame cannot be larger than a complete frame of the same fiber. -/
theorem cardinality_le_complete_frame : Fintype.card J ≤ Fintype.card I :=
  Fintype.card_le_of_injective _ (completeSubframeEmbedding E a ha a').injective

end FLT.Mazur.RelativeOrderedTuples
