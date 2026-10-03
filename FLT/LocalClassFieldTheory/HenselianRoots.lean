/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.FieldTheory.Separable
public import Mathlib.Algebra.Polynomial.Splits

/-!
# Lifting simple roots and splitting over a Henselian local domain

A monic polynomial with separable split reduction splits over the ring
itself. Distinct residue roots lift to distinct roots, so root counting
establishes splitting without a normality assumption.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open Polynomial IsLocalRing

variable {S : Type*} [CommRing S] [HenselianLocalRing S]

/-- Every simple residue root of a monic polynomial lifts uniquely. -/
theorem existsUnique_root_of_residue (P : S[X]) (hP : P.Monic)
    (a : ResidueField S) (ha : (P.map (residue S)).IsRoot a)
    (hd : (P.map (residue S)).derivative.eval a ≠ 0) :
    ∃! x : S, P.IsRoot x ∧ residue S x = a := by
  obtain ⟨x, hx⟩ := residue_surjective (R := S) a
  have he : P.eval x ∈ maximalIdeal S := by
    rw [← residue_eq_zero_iff, ← eval_map_apply, hx]
    exact ha
  have hu : IsUnit (P.derivative.eval x) := by
    rw [← residue_ne_zero_iff_isUnit, ← eval_map_apply, ← derivative_map, hx]
    exact hd
  obtain ⟨y, hy, hyx⟩ := HenselianLocalRing.is_henselian P hP x he hu
  have hyr : residue S y = a := by
    rw [← hx, ← sub_eq_zero, ← map_sub]
    exact (residue_eq_zero_iff _).mpr hyx
  refine ⟨y, ⟨hy, hyr⟩, ?_⟩
  rintro z ⟨hz, hzr⟩
  apply eq_of_eval_eq_zero_of_not_isUnit_sub hz hy
  · change z - y ∈ maximalIdeal S
    rw [← residue_eq_zero_iff, map_sub, hzr, hyr, sub_self]
  · rw [← residue_ne_zero_iff_isUnit, ← eval_map_apply, ← derivative_map, hzr]
    exact hd

/-- A monic polynomial with separable split reduction splits in the Henselian domain. -/
theorem splits_of_separable_residue [IsDomain S] (P : S[X]) (hP : P.Monic)
    (hsep : (P.map (residue S)).Separable)
    (hsplit : (P.map (residue S)).Splits) : P.Splits := by
  classical
  let q := P.map (residue S)
  have hq : q ≠ 0 := (hP.map _).ne_zero
  have lift (a : ↥q.roots.toFinset) : ∃ x : S, P.IsRoot x ∧ residue S x = a := by
    have ha : q.IsRoot a := (mem_roots hq).mp (Multiset.mem_toFinset.mp a.2)
    exact (existsUnique_root_of_residue P hP a ha
      (hsep.eval₂_derivative_ne_zero (RingHom.id _) ha)).exists
  choose f hf using lift
  have hinj : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    exact (hf a).2.symm.trans ((congrArg (residue S) h).trans (hf b).2)
  let t : Finset S := Finset.univ.image f
  have ht : ∀ x ∈ t, P.eval x = 0 := by
    intro x hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    exact (hf a).1
  have hc : t.card = P.natDegree := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_coe,
      Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep),
      ← hsplit.natDegree_eq_card_roots, hP.natDegree_map]
  rw [splits_iff_card_roots, roots_eq_of_natDegree_le_card_of_ne_zero ht hc.ge hP.ne_zero]
  exact hc

end LocalClassFieldTheory
