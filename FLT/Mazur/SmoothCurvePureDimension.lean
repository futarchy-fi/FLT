/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CurveFiberHypotheses
public import FLT.Mazur.SmoothCurveDimension
public import Mathlib.Topology.NoetherianSpace

/-!
# Pure dimension of noetherian smooth curves

Every irreducible component of a noetherian space contains a nonempty open
subset. For a smooth relative curve that open has dimension one, so each
component has dimension one as well.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FLT.Mazur.FCurve

set_option backward.isDefEq.respectTransparency false

universe u

/-- Noetherian smooth relative curves have dimension one on every irreducible component. -/
theorem smoothCurvePureDimension {K : Type u} [Field K] {X : Scheme.{u}}
    [NoetherianSpace X] (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f] :
    CurveFiberHypotheses.PureDimensionOne X := by
  intro Z hZ
  obtain ⟨o, ho, hne, hoZ⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent Z hZ
  let U : X.Opens := ⟨o, ho⟩
  let _ : Nonempty X := hne.nonempty
  let _ : Nonempty U.toScheme := hne.to_subtype
  have hX := smoothCurveDimension f inferInstance inferInstance
  have hU : SmoothOfRelativeDimension 1 (U.ι ≫ f) :=
    IsZariskiLocalAtSource.comp (P := @SmoothOfRelativeDimension.{u} 1) inferInstance U.ι
  have hdU := smoothCurveDimension (U.ι ≫ f) hU inferInstance
  apply le_antisymm ((topologicalKrullDim_subspace_le X Z).trans hX.le)
  rw [← hdU]
  exact (U.isOpenEmbedding'.isInducing.codRestrict (fun x ↦ hoZ x.property)).topologicalKrullDim_le

end FLT.Mazur.FCurve
