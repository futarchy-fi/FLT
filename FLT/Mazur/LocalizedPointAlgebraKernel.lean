/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Ideal

/-!
# Localizing the equations of a point algebra

For a map into field-valued functions, restricting to the points where a
coordinate is nonzero computes the localized kernel. A single multiplication
by that coordinate kills the discarded points; no finite-index hypothesis is needed.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.LocalizedPointAlgebra

variable {R B K ι : Type*} [CommRing R] [CommRing B] [Field K]
  [Algebra R B] [Algebra R K] (f : B →ₐ[R] (ι → K)) (r : B)

/-- The points retained by a principal open. -/
abbrev Index := {i : ι // f r i ≠ 0}

/-- Restriction of the original evaluation map to the retained points. -/
def restriction : B →ₐ[R] (Index f r → K) :=
  AlgHom.pi fun i => (Pi.evalAlgHom R (fun _ : ι => K) i.1).comp f

/-- The inverted coordinate is a unit at every retained point. -/
theorem restriction_isUnit : IsUnit (restriction f r r) :=
  Pi.isUnit_iff.mpr fun i => isUnit_iff_ne_zero.mpr i.2

/-- Evaluation on the principal open. -/
def evaluation : Localization.Away r →ₐ[R] (Index f r → K) :=
  IsLocalization.Away.liftAlgHom r (restriction_isUnit f r)

/-- Localized evaluation extends the original evaluations pointwise. -/
@[simp] theorem evaluation_algebraMap (b : B) (i : Index f r) :
    evaluation f r (algebraMap B (Localization.Away r) b) i = f b i.1 := by
  change IsLocalization.Away.lift r (restriction_isUnit f r)
    (algebraMap B (Localization.Away r) b) i = _
  rw [IsLocalization.Away.lift_eq]
  rfl

/-- Localizing the equations is exactly restricting to the surviving points. -/
theorem kernel_evaluation :
    RingHom.ker (evaluation f r).toRingHom =
      (RingHom.ker f.toRingHom).map (algebraMap B (Localization.Away r)) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨b, s, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers r) z
    have hb : algebraMap B (Localization.Away r) b ∈
        RingHom.ker (evaluation f r).toRingHom :=
      IsLocalization.mk'_mem_iff.mp hz
    have hb' (i : Index f r) : f b i.1 = 0 := by
      have h := congrFun hb i
      change evaluation f r (algebraMap B (Localization.Away r) b) i = 0 at h
      rwa [evaluation_algebraMap] at h
    apply (IsLocalization.mk'_mem_map_algebraMap_iff (Submonoid.powers r) _ _ _ _).mpr
    refine ⟨r, Submonoid.mem_powers r, ?_⟩
    change f (r * b) = 0
    ext i
    rw [map_mul, Pi.mul_apply, Pi.zero_apply]
    by_cases hi : f r i = 0
    · rw [hi, zero_mul]
    · rw [hb' ⟨i, hi⟩, mul_zero]
  · apply Ideal.map_le_iff_le_comap.mpr
    intro b hb
    change evaluation f r (algebraMap B (Localization.Away r) b) = 0
    ext i
    rw [evaluation_algebraMap]
    exact congrFun hb i.1

end FLT.Mazur.LocalizedPointAlgebra
