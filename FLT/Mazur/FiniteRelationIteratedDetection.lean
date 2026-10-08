/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationIteratedStages

/-!
# Equality detection after a second localization

Clear the second denominator, then use equality detection in the original
principal relation system. No regularity condition on either denominator is needed.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteRelationIterated

universe u v w

variable (R : Type u) [CommRing R] {P : Type v} [CommRing P] [Algebra R P]
  (I : Ideal P) (r : P) (s : Finset I) (d : FiniteRelationLocalization.Stage I r s)

/-- A section vanishing on the original double open vanishes at a later stage. -/
theorem exists_transition_zero (t : Set.Ici s) (x : Stage R I r s d t)
    (hx : toQuotient R I r s d t x = 0) :
    ∃ (q : Set.Ici s) (htq : t ≤ q), transition R I r s d htq x = 0 := by
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (denominator R I r s d t) x
  have he : algebraMap (FiniteRelationLocalization.Quotient I r) (Quotient R I r s d)
      (FiniteRelationLocalization.toQuotient R I r t.val a) = 0 := by
    have hh := congrArg (toQuotient R I r s d t) ha
    rw [map_mul, hx, zero_mul, toQuotient_algebraMap] at hh
    exact hh.symm
  obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq
    (FiniteRelationLocalization.toQuotient R I r s d) (he.trans (map_zero _).symm)
  have hb : FiniteRelationLocalization.toQuotient R I r t.val
      (denominator R I r s d t ^ m * a) =
        FiniteRelationLocalization.toQuotient R I r t.val 0 := by
    simpa only [map_mul, map_pow, denominator_toQuotient, map_zero, mul_zero] using hm
  obtain ⟨q, htq, hq⟩ := FiniteRelationLocalization.exists_transition_eq R I r t.val
    (denominator R I r s d t ^ m * a) 0 hb
  let q' : Set.Ici s := ⟨q, t.property.trans htq⟩
  have hn : transition R I r s d (show t ≤ q' from htq) x *
      algebraMap _ (Stage R I r s d q') (denominator R I r s d q') ^ n =
      algebraMap _ (Stage R I r s d q') (FiniteRelationLocalization.transition R I r htq a) :=
    by
    have hh := congrArg (transition R I r s d (show t ≤ q' from htq)) ha
    simpa only [map_mul, map_pow, transition_algebraMap, denominator_transition] using hh
  have hz : transition R I r s d (show t ≤ q' from htq) x *
      algebraMap _ (Stage R I r s d q') (denominator R I r s d q') ^ (n + m) = 0 := by
    calc
      _ = algebraMap _ (Stage R I r s d q')
          (FiniteRelationLocalization.transition R I r htq a) *
          algebraMap _ (Stage R I r s d q') (denominator R I r s d q') ^ m := by
        rw [pow_add, ← mul_assoc, hn]
      _ = algebraMap _ (Stage R I r s d q')
          (FiniteRelationLocalization.transition R I r htq
            (denominator R I r s d t ^ m * a)) := by
        rw [map_mul, map_pow,
          denominator_transition R I r s d (show t ≤ q' from htq),
          map_mul, map_pow, mul_comm]
      _ = 0 := by rw [hq, map_zero, map_zero]
  exact ⟨q', htq,
    ((IsLocalization.Away.algebraMap_isUnit (denominator R I r s d q')).pow
      (n + m)).mul_right_cancel (by simpa only [zero_mul] using hz)⟩

/-- Equality of double-open sections is detected at a later relation stage. -/
theorem exists_transition_eq (t : Set.Ici s) (x y : Stage R I r s d t)
    (h : toQuotient R I r s d t x = toQuotient R I r s d t y) :
    ∃ (q : Set.Ici s) (htq : t ≤ q),
      transition R I r s d htq x = transition R I r s d htq y := by
  obtain ⟨q, htq, hq⟩ := exists_transition_zero R I r s d t (x - y)
    (by rw [map_sub, h, sub_self])
  exact ⟨q, htq, sub_eq_zero.mp (by simpa only [map_sub] using hq)⟩

/-- Finitely many equalities hold together at one double-open model. -/
theorem exists_transition_eq_finite {ι : Type w} [Finite ι] (t : Set.Ici s)
    (x y : ι → Stage R I r s d t)
    (h : ∀ i, toQuotient R I r s d t (x i) = toQuotient R I r s d t (y i)) :
    ∃ (q : Set.Ici s) (htq : t ≤ q),
      ∀ i, transition R I r s d htq (x i) = transition R I r s d htq (y i) := by
  classical
  let _ := Fintype.ofFinite ι
  choose q hq he using fun i ↦ exists_transition_eq R I r s d t (x i) (y i) (h i)
  let k : Set.Ici s := ⟨t.val ∪ Finset.univ.biUnion (fun i ↦ (q i).val),
    t.property.trans Finset.subset_union_left⟩
  have htk : t ≤ k := Finset.subset_union_left
  have hqk (i) : q i ≤ k := by
    intro z hz
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hz⟩)
  refine ⟨k, htk, fun i ↦ ?_⟩
  have hc := transition_comp R I r s d (hq i) (hqk i)
  exact (AlgHom.congr_fun hc (x i)).symm.trans
    ((congrArg (transition R I r s d (hqk i)) (he i)).trans (AlgHom.congr_fun hc (y i)))

end FLT.Mazur.FiniteRelationIterated
