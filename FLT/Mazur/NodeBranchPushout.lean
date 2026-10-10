/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodePinchingDescent

/-!
# The affine split node as a scheme pushout of its full branches

Arbitrary-target descent supplies the universal property in schemes, including
nonaffine targets. The property transports to any specified affine chart isomorphism.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.NodeBranchPushout
universe u
variable (K : Type u) [Field K]

/-- The full affine branches, pinched at their origins, have the node as scheme pushout. -/
theorem isPushout : IsPushout (ProjectiveLine.chartZero K) (ProjectiveLine.chartZero K)
    (PolygonCyclicAtlas.firstBranch K) (PolygonCyclicAtlas.secondBranch K) := by
  have w : ProjectiveLine.chartZero K ≫ PolygonCyclicAtlas.firstBranch K =
      ProjectiveLine.chartZero K ≫ PolygonCyclicAtlas.secondBranch K := by
    rw [PolygonCyclicAtlas.zero_firstBranch, PolygonCyclicAtlas.zero_secondBranch]
  refine ⟨⟨w⟩, ⟨PushoutCocone.IsColimit.mk _
    (fun s => (NodePinchingDescent.node_desc K s.inl s.inr s.condition).choose) ?_ ?_ ?_⟩⟩
  · intro s
    exact (NodePinchingDescent.node_desc K s.inl s.inr s.condition).choose_spec.1.1
  · intro s
    exact (NodePinchingDescent.node_desc K s.inl s.inr s.condition).choose_spec.1.2
  · intro s m hm hn
    exact (NodePinchingDescent.node_desc K s.inl s.inr s.condition).choose_spec.2 m ⟨hm, hn⟩

/-- A specified node-chart comparison transports the entire scheme universal property. -/
theorem isPushout_of_iso {X : Scheme.{u}} (e : PolygonNodeBranches.node K ≅ X) :
    IsPushout (ProjectiveLine.chartZero K) (ProjectiveLine.chartZero K)
      (PolygonCyclicAtlas.firstBranch K ≫ e.hom)
      (PolygonCyclicAtlas.secondBranch K ≫ e.hom) :=
  (isPushout K).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e
    (by simp) (by simp) (by simp) (by simp)

end FLT.Mazur.NodeBranchPushout
