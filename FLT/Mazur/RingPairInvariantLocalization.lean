/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Ring.Subring.Units

/-!
# Localization of the full coefficient equalizer

Localizing both original coefficient rings at an invariant element localizes
exactly their equalizer. Clearing the relation denominator produces an actual
original invariant numerator, even when the restriction maps have kernels.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.RingPairInvariantLocalization
variable {A C A' C' : Type*} [CommRing A] [CommRing C] [CommRing A'] [CommRing C']
  [Algebra A A'] [Algebra C C'] (p q : A →+* C) (p' q' : A' →+* C')
  (hp : ∀ a, p' (algebraMap A A' a) = algebraMap C C' (p a))
  (hq : ∀ a, q' (algebraMap A A' a) = algebraMap C C' (q a))

/-- Restrict original invariant coefficients to the actual localized coefficient equalizer. -/
def restriction : RingHom.eqLocus p q →+* RingHom.eqLocus p' q' :=
  ((algebraMap A A').comp (RingHom.eqLocus p q).subtype).codRestrict _ (fun a ↦ by
    change p' (algebraMap A A' a.val) = q' (algebraMap A A' a.val)
    rw [hp, hq, a.property])

/-- The equalizer algebra uses the original restriction of coefficients. -/
@[instance_reducible]
def invariantAlgebra : Algebra (RingHom.eqLocus p q) (RingHom.eqLocus p' q') :=
  (restriction p q p' q' hp hq).toAlgebra

variable (s : RingHom.eqLocus p q)
  [IsLocalization.Away s.val A'] [IsLocalization.Away (p s.val) C']

include hp hq in
/-- A locally invariant fraction has an original invariant numerator after clearing denominators. -/
theorem invariant_numerator (z : RingHom.eqLocus p' q') :
    ∃ (a : RingHom.eqLocus p q) (n : ℕ),
      z.val * algebraMap A A' (s.val ^ n) = algebraMap A A' a.val := by
  obtain ⟨⟨a, t, n, rfl⟩, ha⟩ := IsLocalization.surj (.powers s.val) z.val
  change z.val * algebraMap A A' (s.val ^ n) = algebraMap A A' a at ha
  have hs : p s.val = q s.val := s.property
  have hz : p' z.val = q' z.val := z.property
  have he : algebraMap C C' (p a) = algebraMap C C' (q a) := by
    rw [← hp, ← hq, ← ha, map_mul, map_mul, hp, hq, map_pow, map_pow,
      hs, hz, map_pow, map_pow]
  obtain ⟨⟨t, m, rfl⟩, hm⟩ := IsLocalization.exists_of_eq (M := .powers (p s.val)) he
  have hm' : p (s.val ^ m * a) = q (s.val ^ m * a) := by
    simpa only [map_mul, map_pow, ← hs] using hm
  refine ⟨⟨s.val ^ m * a, hm'⟩, n + m, ?_⟩
  rw [pow_add, map_mul, ← mul_assoc, ha, map_mul]
  exact mul_comm _ _

/-- The full localized equalizer is a localization of the original full invariant ring. -/
theorem isLocalization :
    let _ := invariantAlgebra p q p' q' hp hq
    IsLocalization.Away s (RingHom.eqLocus p' q') := by
  let _ := invariantAlgebra p q p' q' hp hq
  constructor; constructor
  · rintro ⟨_, n, rfl⟩
    apply (RingHom.isUnit_eqLocus_mk_iff p' q' _).mpr
    change IsUnit (algebraMap A A' (s.val ^ n))
    exact IsLocalization.map_units A' (⟨s.val ^ n, n, rfl⟩ : Submonoid.powers s.val)
  · intro z
    obtain ⟨a, n, ha⟩ := invariant_numerator p q p' q' hp hq s z
    exact ⟨⟨a, s ^ n, n, rfl⟩, Subtype.ext ha⟩
  · intro a b h
    have hh : algebraMap A A' a.val = algebraMap A A' b.val := congrArg Subtype.val h
    obtain ⟨⟨t, n, rfl⟩, hn⟩ := IsLocalization.exists_of_eq (M := .powers s.val) hh
    exact ⟨⟨s ^ n, n, rfl⟩, Subtype.ext hn⟩

/-- Canonical multiplicative identification with the localized original invariant coefficients. -/
def equivalence :
    let _ := invariantAlgebra p q p' q' hp hq
    Localization.Away s ≃ₐ[RingHom.eqLocus p q] RingHom.eqLocus p' q' := by
  let _ := invariantAlgebra p q p' q' hp hq
  let _ := isLocalization p q p' q' hp hq s
  exact IsLocalization.algEquiv (.powers s) _ _

/-- Original invariant coefficients retain their original restriction under this comparison. -/
theorem equivalence_algebraMap (a : RingHom.eqLocus p q) :
    (equivalence p q p' q' hp hq s (algebraMap _ (Localization.Away s) a)).val =
      algebraMap A A' a.val := by
  let _ := invariantAlgebra p q p' q' hp hq
  exact congrArg Subtype.val ((equivalence p q p' q' hp hq s).commutes a)

end FLT.Mazur.RingPairInvariantLocalization
