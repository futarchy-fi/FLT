/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeCoproductCohomology
public import FLT.Mazur.PolygonDirectImageCohomology
/-!
# H1 vanishing for the polygon normalization sequence

The affine direct-image comparison and the source coproduct calculation
prove vanishing for the exact normalization and node module sheaves.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
@[expose] public noncomputable section
universe u
namespace FLT.Mazur.PolygonNormalizationHOne
open FCurve PolygonPinching PolygonStructureInclusion PolygonBranchDifferenceSheaf
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
include h in
/-- The actual normalization direct image is acyclic in positive degrees. -/
theorem normalization_positive (r : ℕ) :
    Subsingleton (ModuleScalarH C.hom (normalizationModule K n p) (r + 1)) :=
  (PolygonDirectImageCohomology.normalization_positive_iff K n hn p q h r).mpr
    (SchemeCoproductCohomology.components_positive K n r)
include h in
/-- The degree-one normalization target in H8. -/
theorem normalization_h1 :
    Subsingleton (ModuleScalarH C.hom (normalizationModule K n p) 1) :=
  normalization_positive K n hn p q h 0
include h in
/-- The degree-one node target in H9. -/
theorem node_h1 : Subsingleton (ModuleScalarH C.hom (nodeModule K n q) 1) :=
  PolygonDirectImageCohomology.node_positive K n hn p q h 0
end FLT.Mazur.PolygonNormalizationHOne
