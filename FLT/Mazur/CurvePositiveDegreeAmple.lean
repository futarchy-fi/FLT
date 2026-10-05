/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CurvePositiveDegreeCohomologyVanishing
public import FLT.Mazur.IdealCohomologyAmpleCriterion

/-!
# Positive degree implies ampleness on a proper integral curve

The ideal-twist vanishing theorem now feeds the closed-point lifting
criterion, yielding the actual affine-section-open definition of ampleness.
-/

@[expose] public noncomputable section

open AlgebraicGeometry TopologicalSpace

namespace FLT.Mazur.FCurve

variable {k : Type} [Field k] {X : Scheme} [IsIntegral X]
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
  (hd : topologicalKrullDim X ≤ 1)

include hd in
/-- A positive-degree line on a proper integral curve is ample. -/
theorem ampleLineBundle_of_curveSheafDegree_pos {L : X.Modules}
    (hL : LocallyFreeRankOne L) (hdeg : 0 < curveSheafDegree f L) : AmpleLineBundle L :=
  ampleLineBundle_of_ideal_h1_vanishing f hL
    (fun I ↦ exists_positive_ideal_power_cohomology_vanishing f hd hL hdeg I 0)

end FLT.Mazur.FCurve
