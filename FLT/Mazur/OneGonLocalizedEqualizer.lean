/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NodeLocalizedEqualizer

/-!
# Localizing the one-gon equalizer near its node

For a denominator with endpoint values one, equality of the endpoint values
of a fraction is exactly equality of the endpoint values of its numerator.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open Polynomial

namespace FLT.Mazur.OneGonLocalizedEqualizer

open PolygonNodePresentation NodeLocalizedEqualizer

variable {K : Type*} [Field K] (s : B (R := K)) (hs : bEval s = 1)

include hs in
theorem zero_value : s.val.eval 0 = 1 := hs

include hs in
theorem one_value : s.val.eval 1 = 1 := ((mem_B _).mp s.property).symm.trans hs

/-- The first endpoint evaluation on the localized normalization. -/
def evalZero : Localization.Away s.val →+* K := evaluation s.val 0 (zero_value s hs)

/-- The second endpoint evaluation on the localized normalization. -/
def evalOne : Localization.Away s.val →+* K := evaluation s.val 1 (one_value s hs)

/-- Localized normalization functions with equal endpoint values. -/
def E : Subring (Localization.Away s.val) := (evalZero s hs).eqLocus (evalOne s hs)

/-- The specified restriction from the one-gon coordinate ring. -/
def restriction : B (R := K) →+* E s hs :=
  ((algebraMap K[X] (Localization.Away s.val)).comp (B (R := K)).val.toRingHom).codRestrict
    (E s hs) fun a ↦ by
      change evalZero s hs _ = evalOne s hs _
      simpa [evalZero, evalOne] using (mem_B _).mp a.property

instance : Algebra (B (R := K)) (E s hs) := (restriction s hs).toAlgebra

/-- Clearing a normalized denominator does not change either endpoint value. -/
theorem eval_of_fraction (z : Localization.Away s.val) (p : K[X]) (n : ℕ)
    (h : z * algebraMap _ (Localization.Away s.val) s.val ^ n = algebraMap _ _ p) :
    evalZero s hs z = p.eval 0 ∧ evalOne s hs z = p.eval 1 := by
  constructor
  · simpa [evalZero, zero_value s hs] using congrArg (evalZero s hs) h
  · simpa [evalOne, one_value s hs] using congrArg (evalOne s hs) h

/-- A fraction is in the equalizer exactly when its numerator is in B. -/
theorem fraction_mem_iff (z : Localization.Away s.val) (p : K[X]) (n : ℕ)
    (h : z * algebraMap _ (Localization.Away s.val) s.val ^ n = algebraMap _ _ p) :
    z ∈ E s hs ↔ p.eval 0 = p.eval 1 := by
  change evalZero s hs z = evalOne s hs z ↔ _
  rw [(eval_of_fraction s hs z p n h).1, (eval_of_fraction s hs z p n h).2]

/-- The localized endpoint equalizer is the localization of B at s. -/
instance isLocalization : IsLocalization.Away s (E s hs) := by
  apply IsLocalization.Away.mk
  · apply (RingHom.isUnit_eqLocus_mk_iff _ _ _).mpr
    exact IsLocalization.Away.algebraMap_isUnit s.val
  · intro z
    obtain ⟨n, p, hp⟩ := IsLocalization.Away.surj s.val z.val
    have hmem : p ∈ B (R := K) :=
      (mem_B p).mpr ((fraction_mem_iff s hs z.val p n hp).mp z.property)
    exact ⟨n, ⟨p, hmem⟩, Subtype.ext hp⟩
  · intro a b h
    have hab := congrArg (fun z : E s hs ↦ z.val) h
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq s.val hab
    exact ⟨n, Subtype.ext hn⟩

/-- The canonical isomorphism from the localization of the actual one-gon ring. -/
def equiv : Localization.Away s ≃+* E s hs :=
  (IsLocalization.algEquiv (Submonoid.powers s) (Localization.Away s) (E s hs)).toRingEquiv

@[simp]
theorem equiv_algebraMap (a : B (R := K)) :
    equiv s hs (algebraMap _ (Localization.Away s) a) = restriction s hs a :=
  (IsLocalization.algEquiv (Submonoid.powers s) (Localization.Away s) (E s hs)).commutes a

/-- Restriction to the normalization is the specified localization map. -/
theorem equiv_restriction :
    (E s hs).subtype.comp (equiv s hs).toRingHom =
      IsLocalization.Away.lift s
        (g := (algebraMap K[X] (Localization.Away s.val)).comp (B (R := K)).val.toRingHom)
        (by exact IsLocalization.Away.algebraMap_isUnit s.val) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers s)
  ext a
  simp [restriction]

end FLT.Mazur.OneGonLocalizedEqualizer
