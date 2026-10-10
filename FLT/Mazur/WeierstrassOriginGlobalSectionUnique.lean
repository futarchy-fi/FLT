/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassOriginGlobalPoleSections

/-!
# Uniqueness of the original global pole section

The actual puncture restriction is injective even over nonreduced rings.
Consequently a positive origin-line section is determined by its affine
restriction, and the global extension of a bounded-pole function is unique.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.AffineImmersionSectionCoordinates
open FLT.Mazur.ModuleSheafBinarySections

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The actual puncture detects positive-line sections on the original neighborhood. -/
theorem originImageSection_restrict_injective (n : ℕ) :
    Function.Injective (res (originDivisorLine W n) (originOverlapOpen_le_image W)) := by
  intro s t h
  apply (originImageNumerator W n).injective
  apply (coordinates (originNeighborhoodInclusion W)).injective
  apply originPunctureRestriction_injective W
  change algebraMap (OriginNeighborhood W) (OriginPuncture W) (originImageNumeratorRing W n s) =
    algebraMap (OriginNeighborhood W) (OriginPuncture W) (originImageNumeratorRing W n t)
  rw [← originOverlapNumerator_image, ← originOverlapNumerator_image, h]

/-- Global positive origin-line sections are determined by the actual affine chart. -/
theorem originGlobalSection_affine_injective (n : ℕ) :
    Function.Injective (res (originDivisorLine W n)
      (show (originAffineOpen W).1 ≤ ⊤ from le_top)) := by
  intro s t h
  have hi : res (originDivisorLine W n) (show (originImageOpen W).1 ≤ ⊤ from le_top) s =
      res (originDivisorLine W n) le_top t := by
    apply originImageSection_restrict_injective W n
    rw [res_res, res_res]
    have hh := congrArg (res (originDivisorLine W n) (originOverlapOpen_le_affine W)) h
    simpa only [res_res] using hh
  exact TopCat.Sheaf.eq_of_locally_eq₂
    (⟨(originDivisorLine W n).presheaf, (originDivisorLine W n).isSheaf⟩ : TopCat.Sheaf Ab _)
    (homOfLE (show (originImageOpen W).1 ≤ ⊤ from le_top))
    (homOfLE (show (originAffineOpen W).1 ≤ ⊤ from le_top))
    (originImageOpen_sup_affine W).ge s t hi h

/-- A bounded original function has exactly one global positive-line extension. -/
theorem originPole_existsUnique_global_section (n : ℕ) (a : Coordinate W 2)
    (ha : HasOriginPoleBound W a n) :
    ∃! s : Γ(originDivisorLine W n, ⊤),
      res (originDivisorLine W n) le_top s = originAffinePoleSection W n a := by
  obtain ⟨s, hs⟩ := originPole_exists_global_section W n a ha
  exact ⟨s, hs, fun t ht ↦ originGlobalSection_affine_injective W n (ht.trans hs.symm)⟩

/-- The unique extension into the actual positive origin-divisor line. -/
def originPoleGlobalSection (n : ℕ) (a : Coordinate W 2) (ha : HasOriginPoleBound W a n) :
    Γ(originDivisorLine W n, ⊤) := (originPole_exists_global_section W n a ha).choose

/-- The extension retains exactly the supplied affine function. -/
theorem originPoleGlobalSection_affine (n : ℕ) (a : Coordinate W 2)
    (ha : HasOriginPoleBound W a n) :
    res (originDivisorLine W n) le_top (originPoleGlobalSection W n a ha) =
      originAffinePoleSection W n a := (originPole_exists_global_section W n a ha).choose_spec

end FLT.Mazur.WeierstrassIntegralChart
