/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticCompleteClosedFiber
public import FLT.Mazur.PolygonArithmeticFamilyFlatness
public import FLT.Mathlib.AlgebraicGeometry.Morphisms.SmoothLocusBaseChange

/-!
# Smooth closed-fiber points of the actual complete polygon family

Flatness and the cartesian closed-fiber comparison identify the inverse image
of the actual smooth locus with the original polygon's smooth locus.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  [IsAdicComplete (ideal A π) A] (n : ℕ) (h : 2 ≤ n) [NeZero n]

local notation "K" => IsLocalRing.ResidueField A

/-- The original complete structural morphism is locally finitely presented. -/
theorem exactVeroneseProjToBase_lfp :
    LocallyOfFinitePresentation (exactVeroneseProjToBase A π n h hne hgen) := by
  let _ := exactVeroneseProjToBase_isProper A π n h hne hgen
  infer_instance

attribute [local instance] exactVeroneseProjToBase_lfp PolygonPinching.cyclic_lfp

/-- Smoothness at an original polygon point is smoothness in the actual total family. -/
theorem completeClosedFiber_preimage_smoothLocus :
    completeClosedFiberInclusion A π hne hgen n h ⁻¹ᵁ
      (exactVeroneseProjToBase A π n h hne hgen).smoothLocus =
      (PolygonCyclicAtlas.toBase K n h).smoothLocus := by
  let _ := exactVeroneseProjToBase_flat A π hne hgen n h
  rw [← completeClosedFiberIso_fst, Scheme.Hom.comp_preimage,
    Scheme.Hom.preimage_smoothLocus_baseChange, Scheme.Hom.preimage_smoothLocus_eq]
  congr 1
  exact completeClosedFiberIso_snd A π hne hgen n h

/-- Every smooth original closed-fiber point is smooth in the complete family. -/
theorem completeClosedFiber_mem_smoothLocus (x : PolygonCyclicAtlas.scheme K n h) :
    completeClosedFiberInclusion A π hne hgen n h x ∈
      (exactVeroneseProjToBase A π n h hne hgen).smoothLocus ↔
      x ∈ (PolygonCyclicAtlas.toBase K n h).smoothLocus := by
  change x ∈ completeClosedFiberInclusion A π hne hgen n h ⁻¹ᵁ
    (exactVeroneseProjToBase A π n h hne hgen).smoothLocus ↔ _
  rw [completeClosedFiber_preimage_smoothLocus]

/-- Every generization of a smooth closed-fiber point remains smooth in the actual family. -/
theorem completeClosedFiber_generization_smooth
    (x : PolygonCyclicAtlas.scheme K n h)
    (hx : x ∈ (PolygonCyclicAtlas.toBase K n h).smoothLocus)
    (y : exactVeroneseProj A π n h hne hgen)
    (hy : y ⤳ completeClosedFiberInclusion A π hne hgen n h x) :
    y ∈ (exactVeroneseProjToBase A π n h hne hgen).smoothLocus :=
  hy.mem_open (exactVeroneseProjToBase A π n h hne hgen).smoothLocus.isOpen
    ((completeClosedFiber_mem_smoothLocus A π hne hgen n h x).mpr hx)

end FLT.Mazur.PolygonArithmeticStages
