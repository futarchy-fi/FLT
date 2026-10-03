/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonGlobalPushout
public import FLT.Mazur.PolygonAtlasCocone

/-!
# The pinching pushout for every positive polygon size

Transport the one-gon and cyclic pushouts through the specified atlas
identifications, preserving the normalization and node maps exactly.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.PolygonAtlas
variable (K : Type u) [Field K]

/-- The specified atlas cocone is a pinching pushout for every positive n. -/
theorem isPushout (n : ℕ) [NeZero n] (hn : 0 < n) :
    IsPushout (PolygonPinching.toComponents K n hn) (PolygonPinching.toNodes K n)
      (normalization K n) (nodes K n) := by
  by_cases h : 2 ≤ n
  · exact (PolygonCyclicPushout.isPushout K n h hn).of_iso'
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (cyclicIso K n h)
      (by simp) (by simp) (by simp) (by simp)
  · have he : n = 1 := by omega
    subst n
    exact (OneGonGlobalPushout.isPushout K hn).of_iso'
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (oneGonIso K)
      (by simp) (by simp) (by simp) (by simp)

end FLT.Mazur.PolygonAtlas
