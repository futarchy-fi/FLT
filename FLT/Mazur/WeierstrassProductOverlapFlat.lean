/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassProductOverlap
public import FLT.Mazur.WeierstrassInfinityProductFlat

/-!
# Flat chart changes and injective infinity product overlap

Both maps into a simultaneous chart overlap are flat. For the infinity charts,
regularity of Z makes the restriction injective, even over nonreduced bases.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Every principal chart restriction is flat. -/
theorem overlapRestriction_flat (j k : Fin 3) :
    (overlapRestriction W j k).toRingHom.Flat :=
  RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ (Submonoid.powers (coord W j k)))

/-- The simultaneous restriction of two input charts is flat. -/
theorem productOverlapRestriction_flat (j k j' k' : Fin 3) :
    (productOverlapRestriction W j k j' k').toRingHom.Flat :=
  (overlapRestriction_flat W j j').tensorProductMap (overlapRestriction_flat W k k')

/-- The normalized input chart map into the same overlap is also flat. -/
theorem productOverlapOther_flat (j k j' k' : Fin 3) :
    (productOverlapOther W j k j' k').toRingHom.Flat := by
  rw [← productOverlapEquiv_restriction]
  exact (productOverlapRestriction_flat W j' k' j k).comp
    (RingHom.Flat.of_bijective (productOverlapEquiv W j k j' k').bijective)

/-- The infinity chart embeds in its overlap with the affine chart. -/
theorem infinityOverlapRestriction_injective :
    Function.Injective (overlapRestriction W 1 2) := by
  apply IsLocalization.injective (Overlap W 1 2)
    (M := Submonoid.powers (coord W 1 2))
  rintro x ⟨n, rfl⟩
  exact ((infinityChart_coord_z_regular W).pow n).mem_nonZeroDivisors

/-- The infinity/affine overlap is flat over the original coefficient ring. -/
theorem infinityOverlap_flat : Module.Flat R (Overlap W 1 2) := by
  let _ := infinityChart_flat W
  exact Module.Flat.trans R (Coordinate W 1) (Overlap W 1 2)

/-- Tensoring the two actual overlap inclusions remains injective. -/
theorem infinityProductOverlapRestriction_injective :
    Function.Injective (productOverlapRestriction W 1 1 2 2) := by
  let _ := infinityChart_flat W
  let _ := infinityOverlap_flat W
  exact TensorProduct.map_injective_of_flat_flat
    (overlapRestriction W 1 2).toLinearMap (overlapRestriction W 1 2).toLinearMap
    (infinityOverlapRestriction_injective W) (infinityOverlapRestriction_injective W)

/-- Regularity reflects through any injective map into a chart comparison ring. -/
theorem chartRegular_of_injective {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Injective f) {a : A}
    (ha : IsRegular (f a)) : IsRegular a := by
  have hl : IsLeftRegular a := by
    intro x y h
    apply hf
    apply ha.left
    simpa only [← map_mul] using congrArg f h
  exact ⟨hl, fun x y h => hl (by simpa only [mul_comm] using h)⟩

end FLT.Mazur.WeierstrassIntegralChart
