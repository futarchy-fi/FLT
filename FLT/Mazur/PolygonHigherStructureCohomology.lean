/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCohomologyIncidence

/-!
# Higher structure cohomology of the original polygon

The actual normalization sequence and the proved acyclicity of its node
and normalization terms kill all structure cohomology above degree one.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.PolygonHigherStructureCohomology

open FCurve PolygonPinching

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

include h in
/-- The original polygon has no structure cohomology in any degree at least two. -/
theorem higher_subsingleton (r : ℕ) :
    Subsingleton (ModuleH (structureModule C.left) (r + 2)) := by
  let S := PolygonNormalizationComplex.complex K n hn p q h
  have hS := PolygonCohomologyIncidence.abelian_shortExact K n hn p q h
  have hnrm := PolygonNormalizationHOne.normalization_positive K n hn p q h (r + 1)
  have hnode := PolygonDirectImageCohomology.node_positive K n hn p q h r
  have he := moduleScalarH_exact₁ S hS C.hom (r + 1)
  have hz (x : ModuleH (structureModule C.left) (r + 2)) : x = 0 := by
    obtain ⟨y, hy⟩ := (he x).mp (hnrm.elim _ _)
    rw [hnode.elim y 0, map_zero] at hy
    exact hy.symm
  exact ⟨fun x y ↦ (hz x).trans (hz y).symm⟩

end FLT.Mazur.PolygonHigherStructureCohomology
