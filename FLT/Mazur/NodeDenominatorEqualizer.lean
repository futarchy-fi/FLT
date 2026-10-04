/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NodeDenominatorRestriction
public import Mathlib.Algebra.Ring.Subring.Units

/-!
# The split-node equalizer for an unnormalized denominator

The denominator need only have a unit value at the node. Its exact localization
is the equalizer of the two localized branch evaluations, without replacing it
by a normalized denominator or changing the affine chart.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial

namespace FLT.Mazur.NodeDenominatorEqualizer

open PolygonNodeEqualizer PolygonNodePresentation
variable {R : Type*} [CommRing R]

/-- Evaluation extends whenever the denominator has an invertible value. -/
def evaluation (p : R[X]) (a : R) (h : IsUnit (p.eval a)) :
    Localization.Away p →+* R :=
  IsLocalization.Away.lift p (g := evalRingHom a) h

@[simp]
lemma evaluation_algebraMap (p : R[X]) (a : R) (h : IsUnit (p.eval a)) (q : R[X]) :
    evaluation p a h (algebraMap R[X] (Localization.Away p) q) = q.eval a :=
  IsLocalization.Away.lift_eq _ _ _

variable (s : A (R := R)) (hs : IsUnit (aEval s))

include hs in
/-- The second branch has the same invertible denominator value. -/
lemma second_unit : IsUnit ((second s).eval 0) := by
  have hv : (first s).eval 0 = (second s).eval 0 := s.property
  rw [← hv]
  exact hs

/-- First localized branch evaluation. -/
def evalLeft : Localization.Away (first s) →+* R := evaluation (first s) 0 hs

/-- Second localized branch evaluation. -/
def evalRight : Localization.Away (second s) →+* R :=
  evaluation (second s) 0 (second_unit s hs)

/-- Functions on the two normalization refinements agreeing at the node. -/
def E : Subring (Localization.Away (first s) × Localization.Away (second s)) :=
  ((evalLeft s hs).comp (RingHom.fst _ _)).eqLocus
    ((evalRight s hs).comp (RingHom.snd _ _))

/-- Restrict a node polynomial pair to the exact localized equalizer. -/
def restriction : A (R := R) →+* E s hs :=
  (((algebraMap R[X] (Localization.Away (first s))).comp first.toRingHom).prod
    ((algebraMap R[X] (Localization.Away (second s))).comp second.toRingHom)).codRestrict
      (E s hs) fun a ↦ by
        change evalLeft s hs _ = evalRight s hs _
        simpa [evalLeft, evalRight, first, second, inclusion] using (mem_A _).mp a.property

instance : Algebra (A (R := R)) (E s hs) := (restriction s hs).toAlgebra

/-- A common exponent clears both denominators without normalizing their node value. -/
lemma denominators (z : E s hs) :
    ∃ (n : ℕ) (a : A (R := R)), z * restriction s hs s ^ n = restriction s hs a := by
  obtain ⟨n, p, hp⟩ := IsLocalization.Away.surj (first s) z.val.1
  obtain ⟨m, q, hq⟩ := IsLocalization.Away.surj (second s) z.val.2
  have ep : evalLeft s hs z.val.1 * (first s).eval 0 ^ n = p.eval 0 := by
    simpa [evalLeft] using congrArg (evalLeft s hs) hp
  have eq : evalRight s hs z.val.2 * (second s).eval 0 ^ m = q.eval 0 := by
    simpa [evalRight] using congrArg (evalRight s hs) hq
  have hv : (first s).eval 0 = (second s).eval 0 := s.property
  have hpq : (p * first s ^ m).eval 0 = (q * second s ^ n).eval 0 := by
    simp only [eval_mul, eval_pow, ← ep, ← eq, ← hv]
    rw [show evalLeft s hs z.val.1 = evalRight s hs z.val.2 from z.property]
    ring
  let a : A (R := R) := ⟨(p * first s ^ m, q * second s ^ n), hpq⟩
  refine ⟨n + m, a, Subtype.ext (Prod.ext ?_ ?_)⟩
  · change z.val.1 * algebraMap _ _ (first s) ^ (n + m) =
      algebraMap _ _ (p * first s ^ m)
    rw [pow_add, ← mul_assoc, hp, map_mul, map_pow]
  · change z.val.2 * algebraMap _ _ (second s) ^ (n + m) =
      algebraMap _ _ (q * second s ^ n)
    rw [Nat.add_comm, pow_add, ← mul_assoc, hq, map_mul, map_pow]

/-- The exact equalizer is a localization of A at the original denominator. -/
instance isLocalization : IsLocalization.Away s (E s hs) := by
  apply IsLocalization.Away.mk
  · apply (RingHom.isUnit_eqLocus_mk_iff _ _ _).mpr
    exact Prod.isUnit_iff.mpr ⟨IsLocalization.Away.algebraMap_isUnit (first s),
      IsLocalization.Away.algebraMap_isUnit (second s)⟩
  · exact denominators s hs
  · intro a b h
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (first s)
      (congrArg (fun z : E s hs ↦ z.val.1) h)
    obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq (second s)
      (congrArg (fun z : E s hs ↦ z.val.2) h)
    change first s ^ n * first a = first s ^ n * first b at hn
    change second s ^ m * second a = second s ^ m * second b at hm
    refine ⟨n + m, Subtype.ext (Prod.ext ?_ ?_)⟩
    · change first s ^ (n + m) * first a = first s ^ (n + m) * first b
      calc
        _ = first s ^ m * (first s ^ n * first a) := by ring
        _ = first s ^ m * (first s ^ n * first b) := by rw [hn]
        _ = _ := by ring
    · change second s ^ (n + m) * second a = second s ^ (n + m) * second b
      calc
        _ = second s ^ n * (second s ^ m * second a) := by ring
        _ = second s ^ n * (second s ^ m * second b) := by rw [hm]
        _ = _ := by ring

/-- A_f is the ring of matching functions on its actual normalization refinements. -/
def equiv : Localization.Away s ≃+* E s hs :=
  (IsLocalization.algEquiv (Submonoid.powers s) (Localization.Away s) (E s hs)).toRingEquiv

@[simp]
lemma equiv_algebraMap (a : A (R := R)) :
    equiv s hs (algebraMap _ (Localization.Away s) a) = restriction s hs a :=
  (IsLocalization.algEquiv (Submonoid.powers s) (Localization.Away s) (E s hs)).commutes a

/-- The equalizer coordinates agree with the explicit localized branch maps. -/
lemma equiv_branches :
    (E s hs).subtype.comp (equiv s hs).toRingHom =
      (NodeDenominatorRestriction.left s).prod (NodeDenominatorRestriction.right s) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers s)
  ext a <;> simp [restriction, NodeDenominatorRestriction.left,
    NodeDenominatorRestriction.right, LocalizationJointRestriction.restriction,
    IsLocalization.Away.map]

end FLT.Mazur.NodeDenominatorEqualizer
