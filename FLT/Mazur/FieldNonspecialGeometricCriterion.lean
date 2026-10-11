/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeometricAcyclicRankOne
public import FLT.Mazur.CurveLineHigherVanishing
public import FLT.Mazur.SmoothDimensionBound

/-!
# Nonspecial field lines satisfy the intrinsic geometric condition

Actual field cohomology detects the geometric acyclic rank-one predicate.
For a smooth integral proper curve with an ample line, H¹ vanishing suffices
for its positive-cohomology part. This connects geometric existence to the
relative open-locus construction.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.FCurve
open CartierAbel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {k : Type} [Field k] {X : Scheme} (f : X ⟶ Spec (.of k)) [IsProper f]
  (L : X.Modules) (hL : LocallyFreeRankOne L)

include hL

/-- Over a field the intrinsic residue-fiber rank is the actual field dimension. -/
theorem properLineFiberSectionRank_field (t : Spec (.of k)) :
    properLineFiberSectionRank f L t = Module.finrank k (ModuleScalarH f L 0) := by
  let _ := hL.isFinitePresentation
  exact proper_field_cohomology_finrank
    (IsPullback.of_hasPullback f ((Spec (.of k)).fromSpecResidueField t)) L 0

/-- The geometric rank-one condition on a field base is exactly actual cohomology. -/
theorem geometricAcyclicRankOne_field_iff :
    GeometricAcyclicRankOne f L ↔
      (∀ n, Subsingleton (ModuleScalarH f L (n + 1))) ∧
        Module.finrank k (ModuleScalarH f L 0) = 1 := by
  have hv (t : Spec (.of k)) (n : ℕ) :
      Subsingleton (ModuleH ((Scheme.Modules.pullback (f.fiberι t)).obj L) (n + 1)) ↔
        Subsingleton (ModuleScalarH f L (n + 1)) :=
    proper_line_cohomology_field_vanishing_iff
      (IsPullback.of_hasPullback f ((Spec (.of k)).fromSpecResidueField t)) hL (n + 1)
  constructor
  · intro h
    let t := IsLocalRing.closedPoint k
    exact ⟨fun n ↦ (hv t n).mp ((h t).1 n),
      (properLineFiberSectionRank_field f L hL t).symm.trans (h t).2⟩
  · rintro ⟨hz, hr⟩ t
    exact ⟨fun n ↦ (hv t n).mpr (hz n),
      (properLineFiberSectionRank_field f L hL t).trans hr⟩

/-- A nonspecial line on a smooth integral ample curve lies in the geometric open condition. -/
theorem geometricAcyclicRankOne_of_nonspecial [IsIntegral X]
    [SmoothOfRelativeDimension 1 f] {B : X.Modules} (hB : AmpleLineBundle B)
    (hz : Subsingleton (ModuleScalarH f L 1))
    (hr : Module.finrank k (ModuleScalarH f L 0) = 1) :
    GeometricAcyclicRankOne f L := by
  apply (geometricAcyclicRankOne_field_iff f L hL).mpr
  refine ⟨?_, hr⟩
  intro n
  cases n with
  | zero => exact hz
  | succ n =>
    exact curve_line_higher_vanishing f (topologicalKrullDim_le_one_of_smooth f) hB hL n

end FLT.Mazur.FCurve
