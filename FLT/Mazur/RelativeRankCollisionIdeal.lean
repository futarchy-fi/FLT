/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeFrameExactRank
public import FLT.Mazur.SchemeScalarPrincipalNeighborhood

/-!
# Original scalar equations excluding unequal endpoint ranks

The bad set consists of actual pairs with different exact ranks. Its scalar
image defines a radical obstruction ideal. Noncontainment in a scalar prime
constructs one principal neighborhood on which every pair has a common rank.
No finite generation or Noetherianity of the scalar ring is required.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A T : Scheme.{0}} (E : Over A) [Etale E.hom] [IsSeparated E.hom]
  (x y : T ⟶ A)

/-- Actual unequal exact ranks, before taking any scalar image or closure. -/
def rankCollision : Set T :=
  {t | ∃ n m : ℕ, n ≠ m ∧ x t ∈ exactRank E n ∧ y t ∈ exactRank E m}

variable [QuasiCompact E.hom]

/-- Absence of a collision constructs one exact rank for both original endpoints. -/
theorem not_mem_rankCollision_iff (t : T) :
    t ∉ rankCollision E x y ↔ ∃ n, x t ∈ exactRank E n ∧ y t ∈ exactRank E n := by
  constructor
  · intro ht
    obtain ⟨n, hn⟩ := exists_exactRank E (x t)
    obtain ⟨m, hm⟩ := exists_exactRank E (y t)
    have hnm : n = m := by
      by_contra hne
      exact ht ⟨n, m, hne, hn, hm⟩
    exact ⟨n, hn, hnm.symm ▸ hm⟩
  · rintro ⟨n, hx, hy⟩ ⟨a, b, hab, ha, hb⟩
    have han : a = n := by
      by_contra hne
      exact Set.disjoint_left.mp (exactRank_disjoint E hne) ha hx
    have hbn : b = n := by
      by_contra hne
      exact Set.disjoint_left.mp (exactRank_disjoint E hne) hb hy
    exact hab (han.trans hbn.symm)

variable {R : Type} [CommRing R] (s : T ⟶ Spec (.of R))

/-- Scalar functions vanishing on all actual unequal-rank pairs. -/
def rankCollisionIdeal : Ideal R := PrimeSpectrum.vanishingIdeal (s '' rankCollision E x y)

omit [QuasiCompact E.hom] in
/-- The obstruction records precisely the closure of the bad scalar image. -/
theorem rankCollisionIdeal_zeroLocus :
    PrimeSpectrum.zeroLocus (rankCollisionIdeal E x y s : Set R) =
      closure (s '' rankCollision E x y) :=
  PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure _

omit [QuasiCompact E.hom] in
/-- This geometric obstruction is radical even for a nonreduced scalar ring. -/
theorem rankCollisionIdeal_isRadical : (rankCollisionIdeal E x y s).IsRadical :=
  PrimeSpectrum.isRadical_vanishingIdeal _

/-- Membership is exactly the common-rank assertion over the entire principal inverse image. -/
theorem mem_rankCollisionIdeal_iff (r : R) :
    r ∈ rankCollisionIdeal E x y s ↔
      ∀ t : T, s t ∈ PrimeSpectrum.basicOpen r →
        ∃ n, x t ∈ exactRank E n ∧ y t ∈ exactRank E n := by
  rw [rankCollisionIdeal, PrimeSpectrum.mem_vanishingIdeal]
  constructor
  · intro hr t ht
    apply (not_mem_rankCollision_iff E x y t).mp
    exact fun hbad ↦ ht (hr _ ⟨t, hbad, rfl⟩)
  · rintro hr z ⟨t, ht, rfl⟩
    by_contra hrt
    exact (not_mem_rankCollision_iff E x y t).mpr (hr t hrt) ht

/-- A scalar prime avoids the obstruction exactly when a common-rank denominator exists. -/
theorem rankCollisionIdeal_not_le_iff (P : PrimeSpectrum R) :
    ¬ rankCollisionIdeal E x y s ≤ P.asIdeal ↔
      ∃ r : R, r ∉ P.asIdeal ∧
        ∀ t : T, s t ∈ PrimeSpectrum.basicOpen r →
          ∃ n, x t ∈ exactRank E n ∧ y t ∈ exactRank E n := by
  constructor
  · intro h
    obtain ⟨r, hr, hrP⟩ := Set.not_subset.mp h
    exact ⟨r, hrP, (mem_rankCollisionIdeal_iff E x y s r).mp hr⟩
  · rintro ⟨r, hrP, hr⟩ h
    exact hrP (h ((mem_rankCollisionIdeal_iff E x y s r).mpr hr))

/-- Every pair above a scalar outside the obstruction has one common exact rank. -/
theorem same_rank_of_rankCollisionIdeal_not_le (t : T)
    (h : ¬ rankCollisionIdeal E x y s ≤ (s t).asIdeal) :
    ∃ n, x t ∈ exactRank E n ∧ y t ∈ exactRank E n := by
  obtain ⟨r, hr, hsame⟩ := (rankCollisionIdeal_not_le_iff E x y s (s t)).mp h
  exact hsame t hr

end FLT.Mazur.RelativeOrderedTuples
