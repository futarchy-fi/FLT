/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NodeDenominatorEqualizer

/-!
# The one-gon equalizer for the original denominator

For a denominator with a unit endpoint value, B_f is exactly the equalizer of
the two evaluations on the localized normalization. Self-incidence is encoded
by retaining both endpoint evaluations on this single normalization ring.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial

namespace FLT.Mazur.OneGonDenominatorEqualizer

open PolygonNodePresentation NodeDenominatorEqualizer
variable {R : Type*} [CommRing R] (s : B (R := R)) (hs : IsUnit (bEval s))

include hs in
/-- The identified endpoints have the same invertible denominator value. -/
lemma one_unit : IsUnit (s.val.eval 1) := by
  rw [← (mem_B _).mp s.property]
  exact hs

/-- Evaluation at the first endpoint of the localized normalization. -/
def evalZero : Localization.Away s.val →+* R := evaluation s.val 0 hs

/-- Evaluation at the second endpoint of the same localized normalization. -/
def evalOne : Localization.Away s.val →+* R := evaluation s.val 1 (one_unit s hs)

/-- Localized functions whose two endpoint values agree. -/
def E : Subring (Localization.Away s.val) := (evalZero s hs).eqLocus (evalOne s hs)

/-- The original pinched ring maps into its localized endpoint equalizer. -/
def restriction : B (R := R) →+* E s hs :=
  ((algebraMap R[X] (Localization.Away s.val)).comp (B (R := R)).val.toRingHom).codRestrict
    (E s hs) fun a ↦ by
      change evalZero s hs _ = evalOne s hs _
      simpa [evalZero, evalOne] using (mem_B _).mp a.property

instance : Algebra (B (R := R)) (E s hs) := (restriction s hs).toAlgebra

/-- Clearing the same invertible endpoint value preserves the equalizer condition. -/
lemma fraction_mem_iff (z : Localization.Away s.val) (p : R[X]) (n : ℕ)
    (h : z * algebraMap _ (Localization.Away s.val) s.val ^ n = algebraMap _ _ p) :
    z ∈ E s hs ↔ p.eval 0 = p.eval 1 := by
  have h₀ : evalZero s hs z * s.val.eval 0 ^ n = p.eval 0 := by
    simpa [evalZero] using congrArg (evalZero s hs) h
  have h₁ : evalOne s hs z * s.val.eval 0 ^ n = p.eval 1 := by
    simpa [evalOne, (mem_B _).mp s.property] using congrArg (evalOne s hs) h
  change evalZero s hs z = evalOne s hs z ↔ _
  rw [← h₀, ← h₁]
  constructor
  · intro he
    rw [he]
  · exact (hs.pow n).mul_right_cancel

/-- This endpoint equalizer is a localization at the original element of B. -/
instance isLocalization : IsLocalization.Away s (E s hs) := by
  apply IsLocalization.Away.mk
  · apply (RingHom.isUnit_eqLocus_mk_iff _ _ _).mpr
    exact IsLocalization.Away.algebraMap_isUnit s.val
  · intro z
    obtain ⟨n, p, hp⟩ := IsLocalization.Away.surj s.val z.val
    have hm : p ∈ B (R := R) :=
      (mem_B p).mpr ((fraction_mem_iff s hs z.val p n hp).mp z.property)
    exact ⟨n, ⟨p, hm⟩, Subtype.ext hp⟩
  · intro a b h
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq s.val
      (congrArg (fun z : E s hs ↦ z.val) h)
    exact ⟨n, Subtype.ext hn⟩

/-- B_f is the exact endpoint equalizer on its normalization refinement. -/
def equiv : Localization.Away s ≃+* E s hs :=
  (IsLocalization.algEquiv (Submonoid.powers s) (Localization.Away s) (E s hs)).toRingEquiv

@[simp]
lemma equiv_algebraMap (a : B (R := R)) :
    equiv s hs (algebraMap _ (Localization.Away s) a) = restriction s hs a :=
  (IsLocalization.algEquiv (Submonoid.powers s) (Localization.Away s) (E s hs)).commutes a

/-- The equalizer inclusion is the specified normalization restriction. -/
lemma equiv_restriction :
    (E s hs).subtype.comp (equiv s hs).toRingHom = NodeDenominatorRestriction.one s := by
  apply IsLocalization.ringHom_ext (Submonoid.powers s)
  ext a
  simp [restriction, NodeDenominatorRestriction.one, LocalizationJointRestriction.restriction,
    IsLocalization.Away.map]

end FLT.Mazur.OneGonDenominatorEqualizer
