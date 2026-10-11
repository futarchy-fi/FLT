/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteClosedFiber
public import FLT.Mazur.PolygonCompleteFamilyFlatness
public import FLT.Mathlib.AlgebraicGeometry.Morphisms.SmoothLocusBaseChange

/-!
# Smooth closed-fiber points of the actual complete polygon family

Flatness and the cartesian closed-fiber comparison identify the inverse image
of the actual smooth locus with the original polygon's smooth locus.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The original complete structural morphism is locally finitely presented. -/
theorem exactVeroneseProjToBase_lfp :
    LocallyOfFinitePresentation (exactVeroneseProjToBase K n h) := by
  let _ := exactVeroneseProjToBase_isProper K n h
  infer_instance

attribute [local instance] exactVeroneseProjToBase_lfp PolygonPinching.cyclic_lfp

/-- Smoothness at an original polygon point is smoothness in the actual total family. -/
theorem completeClosedFiber_preimage_smoothLocus :
    completeClosedFiberInclusion K n h ⁻¹ᵁ (exactVeroneseProjToBase K n h).smoothLocus =
      (PolygonCyclicAtlas.toBase K n h).smoothLocus := by
  let _ := exactVeroneseProjToBase_flat K n h
  rw [← completeClosedFiberIso_fst, Scheme.Hom.comp_preimage,
    Scheme.Hom.preimage_smoothLocus_baseChange, Scheme.Hom.preimage_smoothLocus_eq]
  congr 1
  exact completeClosedFiberIso_snd K n h

/-- Every smooth original closed-fiber point is smooth in the complete family. -/
theorem completeClosedFiber_mem_smoothLocus (x : PolygonCyclicAtlas.scheme K n h) :
    completeClosedFiberInclusion K n h x ∈ (exactVeroneseProjToBase K n h).smoothLocus ↔
      x ∈ (PolygonCyclicAtlas.toBase K n h).smoothLocus := by
  change x ∈ completeClosedFiberInclusion K n h ⁻¹ᵁ
    (exactVeroneseProjToBase K n h).smoothLocus ↔ _
  rw [completeClosedFiber_preimage_smoothLocus]

/-- Every generization of a smooth closed-fiber point remains smooth in the actual family. -/
theorem completeClosedFiber_generization_smooth
    (x : PolygonCyclicAtlas.scheme K n h)
    (hx : x ∈ (PolygonCyclicAtlas.toBase K n h).smoothLocus)
    (y : exactVeroneseProj K n h)
    (hy : y ⤳ completeClosedFiberInclusion K n h x) :
    y ∈ (exactVeroneseProjToBase K n h).smoothLocus :=
  hy.mem_open (exactVeroneseProjToBase K n h).smoothLocus.isOpen
    ((completeClosedFiber_mem_smoothLocus K n h x).mpr hx)

end FLT.Mazur.PolygonInfinitesimalStages
