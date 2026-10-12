/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonDivisorPowerPullback
public import FLT.Mazur.PolygonInfinitesimalDivisor
public import FLT.Mazur.PolygonInfinitesimalRotation

/-!
# The actual boundary divisor is rotation invariant

The cyclic automorphism pulls the complete product of section ideals back to
the relabeled product. For the original unit-one markings this is the same
Cartier ideal, with all its multiplicities and powers retained.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.PolygonInfinitesimal
open PolygonPinching FCurve
set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (t : R) [Fact (IsNilpotent t)]
  (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Rotation is an actual pullback square over the identity of the original base. -/
theorem rotation_isPullback (a : ZMod n) :
    IsPullback (rotation R t n h a) (toBase R t n h) (toBase R t n h) (𝟙 _) := by
  let _ : IsIso (rotation R t n h a) := (rotationIso R t n h a).isIso_hom
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

/-- The full marked Cartier ideal pulls back with its original unit coordinates relabeled. -/
theorem markingDivisor_rotation (a : ZMod n) (b : Fin n → Rˣ) :
    (markingDivisor R t n h b).comap (rotation R t n h a) =
      markingDivisor R t n h (fun i ↦ b (rotateIndex a i)) := by
  let _ := PolygonInfinitesimalSeparated.separated R t n h
  have hp := section_prod_comap_of_cartesian (rotation_isPullback R t n h a)
    Finset.univ
    (fun i ↦ marking R t n h i (b (rotateIndex a i)))
    (fun i ↦ marking R t n h (rotateIndex a i) (b (rotateIndex a i)))
    (fun i ↦ marking_base R t n h i _)
    (fun i ↦ marking_base R t n h (rotateIndex a i) _)
    (fun i ↦ by rw [marking_rotation, Category.id_comp])
  have he : Function.Bijective (rotateIndex a : Fin n → Fin n) := by
    refine Function.bijective_iff_has_inverse.mpr ⟨rotateIndex (-a), ?_, ?_⟩
    · intro i
      rw [← rotateIndex_add, add_neg_cancel, rotateIndex_zero]
    · intro i
      rw [← rotateIndex_add, neg_add_cancel, rotateIndex_zero]
  change (∏ i, (marking R t n h i (b i)).ker).comap _ = _
  rw [← Equiv.prod_comp (Equiv.ofBijective (rotateIndex a) he)]
  exact hp

/-- The original unit-one boundary is invariant as an ideal sheaf. -/
theorem unitMarkingDivisor_rotation (a : ZMod n) :
    (markingDivisor R t n h (fun _ ↦ 1)).comap (rotation R t n h a) =
      markingDivisor R t n h (fun _ ↦ 1) :=
  markingDivisor_rotation R t n h a (fun _ ↦ 1)

/-- Rotation preserves every power of the original boundary ideal. -/
theorem unitMarkingDivisorPower_rotation (a : ZMod n) (m : ℕ) :
    (markingDivisor R t n h (fun _ ↦ 1) ^ m).comap (rotation R t n h a) =
      markingDivisor R t n h (fun _ ↦ 1) ^ m := by
  rw [idealSheaf_comap_pow, unitMarkingDivisor_rotation]

end FLT.Mazur.PolygonInfinitesimal
