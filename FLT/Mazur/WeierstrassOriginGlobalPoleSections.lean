/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassOriginOverlapNumerator

/-!
# Original pole bounds are global positive-divisor sections

A function on the original affine chart has bounded pole at the origin
exactly when its multiplication section extends to the actual positive line
on the whole cubic. The construction glues on the full chart intersection.
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

/-- A global section with the specified affine restriction supplies a regular pole numerator. -/
theorem originPole_of_global_section (n : ℕ) (a : Coordinate W 2)
    (s : Γ(originDivisorLine W n, ⊤))
    (hs : res (originDivisorLine W n) le_top s = originAffinePoleSection W n a) :
    HasOriginPoleBound W a n := by
  let t := res (originDivisorLine W n) (show (originImageOpen W).1 ≤ ⊤ from le_top) s
  refine ⟨originImageNumeratorRing W n t, (originPole_overlap_iff W n a t).mp ?_⟩
  rw [← hs]
  exact (res_res _ _ _ s).trans (res_res _ _ _ s).symm

/-- A regular original pole numerator glues to a section of the actual global divisor line. -/
theorem originPole_exists_global_section (n : ℕ) (a : Coordinate W 2)
    (ha : HasOriginPoleBound W a n) :
    ∃ s : Γ(originDivisorLine W n, ⊤),
      res (originDivisorLine W n) le_top s = originAffinePoleSection W n a := by
  obtain ⟨b, hb⟩ := ha
  let t := (originImageNumerator W n).symm
    ((coordinates (originNeighborhoodInclusion W)).symm b)
  have ht : originImageNumeratorRing W n t = b := by
    change coordinates (originNeighborhoodInclusion W)
      ((originImageNumerator W n) ((originImageNumerator W n).symm _)) = b
    rw [LinearEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  have hc := (originPole_overlap_iff W n a t).mpr (by simpa only [ht] using hb)
  obtain ⟨s, hs, _⟩ := existsUnique_glue (originDivisorLine W n)
    (originImageOpen_sup_affine W) (originOverlapOpen_eq W)
    (originOverlapOpen_le_image W) (originOverlapOpen_le_affine W)
    t (originAffinePoleSection W n a) hc
  exact ⟨s, hs.2⟩

/-- Explicit original pole bounds are exactly extension to the intrinsic positive divisor line. -/
theorem originPole_global_section_iff (n : ℕ) (a : Coordinate W 2) :
    HasOriginPoleBound W a n ↔
      ∃ s : Γ(originDivisorLine W n, ⊤),
        res (originDivisorLine W n) le_top s = originAffinePoleSection W n a :=
  ⟨originPole_exists_global_section W n a,
    fun ⟨s, hs⟩ ↦ originPole_of_global_section W n a s hs⟩

end FLT.Mazur.WeierstrassIntegralChart
