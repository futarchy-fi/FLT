/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Ring.Subring.Units
/-!
# Localizing a ring equalizer

The localized endpoint ring is localized too. Denominator clearance accounts
for torsion in the base ring and does not assume endpoint values are units.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.RingEqualizerLocalization
variable {C D : Type*} [CommRing C] [CommRing D] (f g : C →+* D)
  (s : f.eqLocus g)
/-- The first ring map extended to the localizations. -/
def evalFirst : Localization.Away s.val →+* Localization.Away (f s.val) :=
  IsLocalization.Away.map _ _ f s.val
/-- The second ring map extended to the same localized target. -/
def evalSecond : Localization.Away s.val →+* Localization.Away (f s.val) :=
  IsLocalization.Away.lift s.val
    (g := (algebraMap D (Localization.Away (f s.val))).comp g)
    (by
      change IsUnit (algebraMap D _ (g s.val))
      rw [← (show f s.val = g s.val from s.property)]
      exact IsLocalization.Away.algebraMap_isUnit (f s.val))
@[simp] theorem evalFirst_algebraMap (p : C) :
    evalFirst f g s (algebraMap C (Localization.Away s.val) p) =
      algebraMap D _ (f p) := by simp [evalFirst, IsLocalization.Away.map]
@[simp] theorem evalSecond_algebraMap (p : C) :
    evalSecond f g s (algebraMap C (Localization.Away s.val) p) =
      algebraMap D _ (g p) := IsLocalization.Away.lift_eq _ _ _
/-- The equalizer of the two localized maps. -/
def E : Subring (Localization.Away s.val) := (evalFirst f g s).eqLocus (evalSecond f g s)
/-- The original equalizer maps to the localized equalizer. -/
def restriction : f.eqLocus g →+* E f g s :=
  ((algebraMap C (Localization.Away s.val)).comp (f.eqLocus g).subtype).codRestrict
    (E f g s) fun a ↦ by
      change evalFirst f g s _ = evalSecond f g s _
      simpa using congrArg (algebraMap D (Localization.Away (f s.val))) a.property
instance : Algebra (f.eqLocus g) (E f g s) := (restriction f g s).toAlgebra

/-- Clear a denominator and the remaining endpoint torsion simultaneously. -/
theorem denominators (z : E f g s) :
    ∃ (n : ℕ) (a : f.eqLocus g), z * restriction f g s s ^ n = restriction f g s a := by
  obtain ⟨n, p, hp⟩ := IsLocalization.Away.surj s.val z.val
  have he : algebraMap D (Localization.Away (f s.val)) (f p) =
      algebraMap D (Localization.Away (f s.val)) (g p) := by
    have h₁ := congrArg (evalFirst f g s) hp
    have h₂ := congrArg (evalSecond f g s) hp
    simp only [map_mul, map_pow, evalFirst_algebraMap, evalSecond_algebraMap,
      ← (show f s.val = g s.val from s.property),
      ← (show evalFirst f g s z.val = evalSecond f g s z.val
        from z.property)] at h₁ h₂
    exact h₁.symm.trans h₂
  obtain ⟨k, hk⟩ := IsLocalization.Away.exists_of_eq (f s.val) he
  let a : f.eqLocus g := ⟨s.val ^ k * p, by
    change f (s.val ^ k * p) = g (s.val ^ k * p)
    simpa only [map_mul, map_pow, ← (show f s.val = g s.val from s.property)] using hk⟩
  refine ⟨n + k, a, Subtype.ext ?_⟩
  change z.val * algebraMap C _ s.val ^ (n + k) = algebraMap C _ (s.val ^ k * p)
  rw [pow_add, ← mul_assoc, hp, map_mul, map_pow, mul_comm]

instance isLocalization : IsLocalization.Away s (E f g s) := by
  apply IsLocalization.Away.mk
  · apply (RingHom.isUnit_eqLocus_mk_iff _ _ _).mpr
    exact IsLocalization.Away.algebraMap_isUnit s.val
  · exact denominators f g s
  · intro a b h
    have hab := congrArg (fun z : E f g s ↦ z.val) h
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq s.val hab
    exact ⟨n, Subtype.ext hn⟩

/-- Localization commutes with the specified ring equalizer. -/
def equiv : Localization.Away s ≃+* E f g s :=
  (IsLocalization.algEquiv (Submonoid.powers s) (Localization.Away s) (E f g s)).toRingEquiv
@[simp] theorem equiv_algebraMap (a : f.eqLocus g) :
    equiv f g s (algebraMap _ (Localization.Away s) a) = restriction f g s a :=
  (IsLocalization.algEquiv (Submonoid.powers s) (Localization.Away s) (E f g s)).commutes a
end FLT.Mazur.RingEqualizerLocalization
