/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSplitNodalGroup
public import FLT.Mazur.EllipticNonsplitNodalGroup
public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point

/-!
# No residue-characteristic torsion in a finite nodal smooth group

The actual smooth point group has order q-1 or q+1. Since the residue prime
divides q, neither group has a nonzero point killed by that prime.
-/

@[expose] public noncomputable section

namespace FLT.Mazur

open WeierstrassCurve

variable {F : Type*} [Field F] [Finite F] (W : WeierstrassCurve F)
  (p : ℕ) [Fact p.Prime] [CharP F p]

/-- The characteristic prime does not divide the actual smooth nodal group order. -/
theorem nodalPoint_card_not_dvd_char (hΔ : W.Δ = 0) (hc : W.c₄ ≠ 0) :
    ¬ p ∣ Nat.card W.toAffine.Point := by
  classical
  let _ := Fintype.ofFinite F
  have hq : p ∣ Fintype.card F :=
    (CharP.cast_eq_zero_iff F p _).mp (Nat.cast_card_eq_zero F)
  intro hd
  apply (Fact.out : p.Prime).not_dvd_one
  by_cases hs : W.nodePoly.Splits
  · rw [splitNodalPoint_card W hΔ hc hs] at hd
    apply (Nat.dvd_add_iff_left hd).mpr
    simpa only [Nat.add_comm 1, Nat.sub_add_cancel Fintype.card_pos] using hq
  · rw [nonsplitNodalPoint_card W hΔ hc hs] at hd
    exact (Nat.dvd_add_iff_left hq).mpr (by simpa only [Nat.add_comm] using hd)

/-- Every smooth affine p-torsion point of a nodal cubic in characteristic p is zero. -/
theorem nodalPoint_char_torsion_eq_zero (hΔ : W.Δ = 0) (hc : W.c₄ ≠ 0)
    [DecidableEq F] (P : W.toAffine.Point) (hP : p • P = 0) : P = 0 := by
  by_contra hne
  have ho : addOrderOf P = p := addOrderOf_eq_prime hP hne
  exact nodalPoint_card_not_dvd_char W p hΔ hc
    (ho ▸ addOrderOf_dvd_natCard P)

/-- The same exclusion holds for the actual smooth projective point group. -/
theorem nodalProjectivePoint_char_torsion_eq_zero (hΔ : W.Δ = 0) (hc : W.c₄ ≠ 0)
    (P : W.toProjective.Point) (hP : p • P = 0) : P = 0 := by
  classical
  let e := Projective.Point.toAffineAddEquiv W
  apply e.injective
  rw [map_zero]
  exact nodalPoint_char_torsion_eq_zero W p hΔ hc (e P)
    (by rw [← map_nsmul, hP, map_zero])

end FLT.Mazur
