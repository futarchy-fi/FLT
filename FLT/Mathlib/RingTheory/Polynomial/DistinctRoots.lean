/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Algebra.Polynomial.Roots

/-!
# Factoring a monic polynomial over an indexed family of roots

A full-degree family of distinct roots determines a monic polynomial.
-/

@[expose] public noncomputable section

open Polynomial

namespace Polynomial

variable {R ι : Type*} [CommRing R] [IsDomain R] [Fintype ι]

/-- A monic polynomial is the product of its distinct indexed roots when
the number of roots is its degree. -/
theorem eqProdOfDistinctRoots (P : R[X]) (hP : P.Monic) (a : ι → R)
    (ha : Function.Injective a) (hroot : ∀ i, P.IsRoot (a i))
    (hdeg : P.natDegree = Fintype.card ι) :
    P = ∏ i, (X - C (a i)) := by
  classical
  let s : Multiset R := Finset.univ.val.map a
  have hs : s.Nodup := Finset.univ.nodup.map ha
  have hsle : s ≤ P.roots := by
    apply (Multiset.le_iff_subset hs).mpr
    intro x hx
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hx
    exact (mem_roots hP.ne_zero).mpr (hroot i)
  have hd := (s.prod_X_sub_C_dvd_iff_le_roots hP.ne_zero).mpr hsle
  have h := eq_of_monic_of_dvd_of_natDegree_le
    (monic_multisetProd_X_sub_C s) hP hd (by
      rw [natDegree_multiset_prod_X_sub_C_eq_card, hdeg]
      simp [s])
  simpa only [s, Multiset.map_map, Function.comp_def, Finset.prod_eq_multiset_prod] using h

end Polynomial
