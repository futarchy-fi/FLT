/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationSubframeRefinement
public import FLT.Mazur.EquivalenceRelationNormalizedFrameEtale

/-!
# Etale geometry of arbitrary moving subframes

Every strict selection is etale: its moving first endpoint is an etale
normalized projection after a label isomorphism. Cancelling the target
projection proves the assertion without requiring complete frames or a unit
degree. The result also holds on independently restricted source and target charts.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J)

include e in
/-- Each moving endpoint is etale, even when it differs from the original base label. -/
theorem second_endpoint_etale (i : I) : Etale (coordinate p q I o i ≫ q) := by
  rw [← labelChange_first e I o i]
  let _ := first_etale e I i
  change Etale ((labelIso e I o i).hom ≫ first p q I i)
  infer_instance

/-- An arbitrary strict subframe selection is etale over its moving endpoint. -/
theorem subframeMap_etale (ι : J ↪ I) : Etale (subframeMap e o o' ι) := by
  let _ := first_etale e J o'
  have : Etale (subframeMap e o o' ι ≫ first p q J o') := by
    rw [subframeMap_first]
    exact second_endpoint_etale e o (ι o')
  exact Etale.of_comp _ (first p q J o')

/-- Independent chart restrictions preserve etaleness of the actual selection. -/
theorem subframeRefinementMap_etale (ι : J ↪ I)
    (U : (source p q I o).Opens) (V : (source p q J o').Opens)
    (hUV : U ≤ subframeMap e o o' ι ⁻¹ᵁ V) :
    Etale (subframeRefinementMap e o o' ι U V hUV) := by
  let _ := subframeMap_etale e o o' ι
  have : Etale (subframeRefinementMap e o o' ι U V hUV ≫ V.ι) := by
    rw [subframeRefinementMap_inclusion]
    infer_instance
  exact Etale.of_comp _ V.ι

end FLT.Mazur.EquivalenceRelationNormalizedFrames
