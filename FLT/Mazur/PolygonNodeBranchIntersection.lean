/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonCyclicCocone
public import FLT.Mazur.SurjectiveKernelPushout
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# The full affine branches meet scheme-theoretically in their common origin

The sum of the two restriction kernels is exactly the origin ideal.
Consequently the whole branch intersection is the base scheme.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits Polynomial
namespace FLT.Mazur.PolygonNodeBranchIntersection
open PolygonNodeEqualizer PolygonNodePresentation PolygonNodeLocalization
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (R : Type u) [CommRing R]

/-- Vanishing at the node is precisely the sum of the two branch restriction ideals. -/
theorem origin_ker : RingHom.ker (aEval (R := R)).toRingHom =
    RingHom.ker (first (R := R)).toRingHom ⊔ RingHom.ker (second (R := R)).toRingHom := by
  apply le_antisymm
  · intro z hz
    have hz0 : (first z).eval 0 = 0 := hz
    let q : A (R := R) := ⟨(first z, 0), (mem_A _).mpr (by simpa using hz0)⟩
    have hq : q ∈ RingHom.ker (second (R := R)).toRingHom := by
      change (0 : R[X]) = 0
      rfl
    have hzq : z - q ∈ RingHom.ker (first (R := R)).toRingHom := by
      change first (z - q) = 0
      rw [map_sub]
      exact sub_self _
    have H := Ideal.add_mem
      (RingHom.ker (first (R := R)).toRingHom ⊔ RingHom.ker (second (R := R)).toRingHom)
      (Ideal.mem_sup_left hzq) (Ideal.mem_sup_right hq)
    simpa only [sub_add_cancel] using H
  · apply sup_le
    · intro z hz
      change (aeval (0 : R)) (first z) = 0
      rw [show first z = 0 from hz, map_zero]
    · intro z hz
      change (aeval (0 : R)) (first z) = 0
      have H := DFunLike.congr_fun (first_second_agree (R := R)) z
      change (aeval (0 : R)) (first z) = (aeval (0 : R)) (second z) at H
      rw [H, show second z = 0 from hz, map_zero]

variable (K : Type u) [Field K]

/-- The entire fiber product of the two complete branches is their original common origin. -/
theorem branches_isPullback :
    IsPullback (ProjectiveLine.chartZero K) (ProjectiveLine.chartZero K)
      (PolygonCyclicAtlas.firstBranch K) (PolygonCyclicAtlas.secondBranch K) := by
  apply isPullback_SpecMap_of_isPushout
  apply SurjectiveKernelPushout.isPushout (first (R := K)).toRingHom
    (second (R := K)).toRingHom (aeval (0 : K)).toRingHom (aeval (0 : K)).toRingHom
    first_surjective second_surjective
  · intro r
    exact ⟨algebraMap K (A (R := K)) r, (aEval (R := K)).commutes r⟩
  · exact congrArg AlgHom.toRingHom (first_second_agree (R := K))
  · exact origin_ker K

end FLT.Mazur.PolygonNodeBranchIntersection
