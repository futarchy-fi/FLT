/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonNodePresentation
public import Mathlib.Algebra.Ring.Subring.Units

/-!
# Localizing the node equalizer near its origin

The two branch evaluations extend across any denominator with value one.
Their pullback is the localization of the specified node ring.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open Polynomial

namespace FLT.Mazur.NodeLocalizedEqualizer

open PolygonNodeEqualizer PolygonNodePresentation

variable {K : Type*} [Field K] (s : A (R := K)) (hs : aEval s = 1)

/-- Evaluation on a localized polynomial ring with normalized denominator. -/
def evaluation (p : K[X]) (a : K) (h : p.eval a = 1) :
    Localization.Away p →+* K :=
  IsLocalization.Away.lift p (g := evalRingHom a)
    (by simpa only [coe_evalRingHom, h] using (isUnit_one : IsUnit (1 : K)))

@[simp]
theorem evaluation_algebraMap (p : K[X]) (a : K) (h : p.eval a = 1) (q : K[X]) :
    evaluation p a h (algebraMap K[X] (Localization.Away p) q) = q.eval a :=
  IsLocalization.Away.lift_eq _ _ _

include hs in
theorem first_value : (first s).eval 0 = 1 := hs

include hs in
theorem second_value : (second s).eval 0 = 1 := by
  exact ((mem_A _).mp s.property).symm.trans hs

/-- Evaluation at the origin on the first localized branch. -/
def evalFirst : Localization.Away (first s) →+* K :=
  evaluation (first s) 0 (first_value s hs)

/-- Evaluation at the origin on the second localized branch. -/
def evalSecond : Localization.Away (second s) →+* K :=
  evaluation (second s) 0 (second_value s hs)

/-- Pairs of localized branch functions agreeing at the origin. -/
def E : Subring (Localization.Away (first s) × Localization.Away (second s)) :=
  ((evalFirst s hs).comp (RingHom.fst _ _)).eqLocus
    ((evalSecond s hs).comp (RingHom.snd _ _))

/-- The specified restriction map from the node ring. -/
def restriction : A (R := K) →+* E s hs :=
  (((algebraMap K[X] (Localization.Away (first s))).comp (first (R := K)).toRingHom).prod
    ((algebraMap K[X] (Localization.Away (second s))).comp (second (R := K)).toRingHom)).codRestrict
      (E s hs) fun a ↦ by
        change evalFirst s hs _ = evalSecond s hs _
        simpa [evalFirst, evalSecond, first, second, inclusion] using (mem_A _).mp a.property

instance : Algebra (A (R := K)) (E s hs) := (restriction s hs).toAlgebra

/-- A common exponent clears the denominators on both branches. -/
theorem denominators (z : E s hs) :
    ∃ (n : ℕ) (a : A (R := K)), z * restriction s hs s ^ n = restriction s hs a := by
  obtain ⟨n, p, hp⟩ := IsLocalization.Away.surj (first s) z.val.1
  obtain ⟨m, q, hq⟩ := IsLocalization.Away.surj (second s) z.val.2
  have ep : evalFirst s hs z.val.1 = p.eval 0 := by
    simpa [evalFirst, first_value s hs] using congrArg (evalFirst s hs) hp
  have eq : evalSecond s hs z.val.2 = q.eval 0 := by
    simpa [evalSecond, second_value s hs] using congrArg (evalSecond s hs) hq
  have hpq : p.eval 0 = q.eval 0 := ep.symm.trans (z.property.trans eq)
  let a : A (R := K) := ⟨(p * first s ^ m, q * second s ^ n), by
    simpa [mem_A, first_value s hs, second_value s hs] using hpq⟩
  refine ⟨n + m, a, Subtype.ext (Prod.ext ?_ ?_)⟩
  · change z.val.1 * algebraMap _ _ (first s) ^ (n + m) =
      algebraMap _ _ (p * first s ^ m)
    rw [pow_add, ← mul_assoc, hp, map_mul, map_pow]
  · change z.val.2 * algebraMap _ _ (second s) ^ (n + m) =
      algebraMap _ _ (q * second s ^ n)
    rw [Nat.add_comm, pow_add, ← mul_assoc, hq, map_mul, map_pow]

/-- The pullback of the localized branches is the localization of the node. -/
instance isLocalization : IsLocalization.Away s (E s hs) := by
  apply IsLocalization.Away.mk
  · apply (RingHom.isUnit_eqLocus_mk_iff _ _ _).mpr
    exact Prod.isUnit_iff.mpr ⟨IsLocalization.Away.algebraMap_isUnit (first s),
      IsLocalization.Away.algebraMap_isUnit (second s)⟩
  · exact denominators s hs
  · intro a b h
    have h₁ := congrArg (fun z : E s hs ↦ z.val.1) h
    have h₂ := congrArg (fun z : E s hs ↦ z.val.2) h
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (first s) h₁
    obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq (second s) h₂
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

/-- The canonical localization isomorphism, with the specified algebra structure. -/
def equiv : Localization.Away s ≃+* E s hs :=
  (IsLocalization.algEquiv (Submonoid.powers s) (Localization.Away s) (E s hs)).toRingEquiv

@[simp]
theorem equiv_algebraMap (a : A (R := K)) :
    equiv s hs (algebraMap _ (Localization.Away s) a) = restriction s hs a :=
  (IsLocalization.algEquiv (Submonoid.powers s) (Localization.Away s) (E s hs)).commutes a

/-- Projection to the first branch is the canonical localization map. -/
theorem equiv_first :
    (RingHom.fst _ _).comp ((E s hs).subtype.comp (equiv s hs).toRingHom) =
      IsLocalization.Away.map (Localization.Away s) (Localization.Away (first s))
        (first (R := K)).toRingHom s := by
  apply IsLocalization.ringHom_ext (Submonoid.powers s)
  ext a
  simp [restriction, IsLocalization.Away.map]

/-- Projection to the second branch is the canonical localization map. -/
theorem equiv_second :
    (RingHom.snd _ _).comp ((E s hs).subtype.comp (equiv s hs).toRingHom) =
      IsLocalization.Away.map (Localization.Away s) (Localization.Away (second s))
        (second (R := K)).toRingHom s := by
  apply IsLocalization.ringHom_ext (Submonoid.powers s)
  ext a
  simp [restriction, IsLocalization.Away.map]

end FLT.Mazur.NodeLocalizedEqualizer
