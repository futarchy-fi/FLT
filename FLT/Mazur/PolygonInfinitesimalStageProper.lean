/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalStageFiber
public import FLT.Mazur.PolygonCyclicPushout
public import FLT.Mazur.PolygonProper

/-!
# Properness of the concrete infinitesimal smoothing stages over a field

The original proper polygon is a surjective closed fiber of the actual
finite-order family. Universal closedness descends through that surjective
inclusion. The previously constructed separatedness and finite presentation
then give properness of the entire infinitesimal stage.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false

variable (K : Type u) [Field K] (m n : ℕ) (h : 2 ≤ n)

/-- Properness of the original cyclic atlas with its specified coefficient morphism. -/
theorem cyclicPolygon_proper : IsProper (PolygonCyclicAtlas.toBase K n h) := by
  let _ : NeZero n := ⟨by omega⟩
  exact PolygonProper.proper K n (by omega) (PolygonCyclicAtlas.normalization K n h)
    (PolygonCyclicAtlas.nodes K n h) (PolygonCyclicPushout.isPushout K n h (by omega))

/-- Every actual finite-order stage is universally closed over its truncated coefficient ring. -/
instance family_universallyClosed : UniversallyClosed (family K m n h).hom := by
  let _ := cyclicPolygon_proper K n h
  have hc : UniversallyClosed
      (specialFiberInclusion K m n h ≫ (family K m n h).hom) := by
    rw [(specialFiberInclusion_isPullback K m n h).w]
    infer_instance
  exact UniversallyClosed.of_comp_surjective (specialFiberInclusion K m n h) _

/-- The concrete smoothing stages are proper, including the two-gon at every order. -/
instance family_proper : IsProper (family K m n h).hom := ⟨⟩

end FLT.Mazur.PolygonInfinitesimalStages
