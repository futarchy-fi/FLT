/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSeparated
public import FLT.Mazur.PolygonNodesClosed
public import FLT.Mazur.PolygonNormalizationHZero
public import FLT.Mazur.CoherentFreeSheaf
public import FLT.Mazur.AffinePushforwardCohomology
/-!
# Cohomology of the polygon direct images

Separatedness permits the affine direct-image comparison. The finite node
coproduct is affine, so its positive-degree cohomology vanishes. Normalization
vanishing is reduced to the source coproduct without assuming that conclusion.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace FLT.Mazur.PolygonDirectImageCohomology
open FCurve PolygonPinching PolygonStructureInclusion PolygonBranchDifferenceSheaf
variable (K : Type u) [Field K] (n : ℕ)
/-- The finite coproduct of nodes is an affine scheme. -/
instance nodes_affine : IsAffine (nodes K n).left := by
  let e : (∐ fun _ : Fin n ↦ (point K).left) ≅ (nodes K n).left :=
    asIso (sigmaComparison (Over.forget (Spec (.of K)))
    (fun _ : Fin n ↦ point K))
  have : IsAffine (∐ fun _ : Fin n ↦ (point K).left) := by
    change IsAffine (∐ fun _ : Fin n ↦ Spec (.of K))
    infer_instance
  exact IsAffine.of_isIso e.inv
/-- The source node coproduct has no positive-degree structure cohomology. -/
theorem nodes_positive (r : ℕ) :
    Subsingleton (ModuleH (structureUnitModule (nodes K n).left) (r + 1)) :=
  affine_moduleH_succ_subsingleton _ r
variable [NeZero n] (hn : 0 < n) {C : Over (Spec (.of K))}
  (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
include h in
/-- Affine direct image reduces normalization vanishing to its actual source. -/
theorem normalization_positive_iff (r : ℕ) :
    Subsingleton (ModuleScalarH C.hom (normalizationModule K n p) (r + 1)) ↔
      Subsingleton (ModuleH (structureUnitModule (components K n).left) (r + 1)) := by
  have := PolygonSeparated.cocone K n hn p q h
  have := PolygonNormalizationFinite.cocone_normalization_finite K n hn p q h
  exact affinePushforward_moduleH_subsingleton_iff p.left _ (r + 1)
include h in
/-- The actual node direct image has no positive-degree scalar cohomology. -/
theorem node_positive (r : ℕ) :
    Subsingleton (ModuleScalarH C.hom (nodeModule K n q) (r + 1)) := by
  have := PolygonSeparated.cocone K n hn p q h
  have := PolygonNodesClosed.cocone K n hn p q h
  exact (affinePushforward_moduleH_subsingleton_iff q.left _ (r + 1)).mpr
    (nodes_positive K n r)
end FLT.Mazur.PolygonDirectImageCohomology
