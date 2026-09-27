/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.TateTorsion

/-!
# Normalized Kummer representatives of Tate torsion

The exponent of a torsion representative can be chosen in `[0,n)`.
These representatives give the geometric points of the Kummer model.
-/

@[expose] public section

open scoped WeierstrassCurve.Affine
open ValuativeRel

namespace WeierstrassCurve

variable {K Ω : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  (E : WeierstrassCurve K) [E.IsElliptic] [E.HasSplitMultiplicativeReduction 𝒪[K]]
  [Field Ω] [Algebra K Ω] [DecidableEq Ω] [Algebra.IsAlgebraic K Ω]

/-- Every Tate torsion point has a representative with exponent between zero and `n - 1`. -/
theorem exists_normalized_tate_torsion_rep {n : ℕ} (hn : 0 < n)
    (P : AddSubgroup.torsionBy (E⁄Ω).Point (n : ℤ)) :
    ∃ (i : Fin n) (x : Ωˣ), E.tatePoint Ω x = P ∧
      x ^ n = E.qUnitSepClosure Ω ^ i.val := by
  obtain ⟨x, m, hx, hm⟩ := E.exists_tatePoint_torsionBy_rep Ω n P
  let q := E.qUnitSepClosure Ω
  have hr0 := Int.emod_nonneg m (show (n : ℤ) ≠ 0 by omega)
  have hrlt := Int.emod_lt_of_pos m (show (0 : ℤ) < n by omega)
  let i : Fin n := ⟨(m % (n : ℤ)).toNat, by omega⟩
  have hi : (i.val : ℤ) = m % (n : ℤ) := by
    dsimp [i]
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  have he : m - (m / (n : ℤ)) * n = (i.val : ℤ) := by
    rw [hi, Int.emod_def, mul_comm (n : ℤ)]
  refine ⟨i, x / q ^ (m / (n : ℤ)), ?_, ?_⟩
  · have hz : E.tatePoint Ω (q ^ (m / (n : ℤ))) = 0 :=
      (E.tatePoint_eq_zero_iff Ω _).mpr (Subgroup.zpow_mem_zpowers _ _)
    have h := E.tatePoint_mul Ω (x / q ^ (m / (n : ℤ))) (q ^ (m / (n : ℤ)))
    simpa only [div_mul_cancel, hz, add_zero, hx] using h.symm
  · dsimp only [q]
    rw [div_pow, hm, ← zpow_natCast, ← zpow_mul, div_eq_mul_inv,
      ← zpow_sub, he, zpow_natCast]

/-- Two normalized Tate torsion representatives giving the same point are equal. -/
theorem normalized_tate_torsion_rep_injective {n : ℕ} (hn : 0 < n)
    {i j : Fin n} {x y : Ωˣ}
    (hx : x ^ n = E.qUnitSepClosure Ω ^ i.val)
    (hy : y ^ n = E.qUnitSepClosure Ω ^ j.val)
    (hxy : E.tatePoint Ω x = E.tatePoint Ω y) : i = j ∧ x = y := by
  have hij := E.tatePoint_exponent_eq Ω (n := n) (a := i.val) (b := j.val)
    (by simpa only [zpow_natCast] using hx)
    (by simpa only [zpow_natCast] using hy) hxy
  have hi : i = j := by
    apply Fin.ext
    have hcast : (i.val : ZMod n) = (j.val : ZMod n) := by
      simpa only [Int.cast_natCast] using hij
    simpa only [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt i.isLt,
      Nat.mod_eq_of_lt j.isLt] using hcast
  subst j
  refine ⟨rfl, ?_⟩
  have hquot : (x : Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω)) = y :=
    (E.tateEquivSepClosure Ω).injective hxy
  obtain ⟨c, hc⟩ := QuotientGroup.eq_iff_div_mem.mp hquot
  dsimp only at hc
  have hc0 : c * (n : ℤ) = 0 := by
    apply (injective_zpow_iff_not_isOfFinOrder.mpr
      (E.qUnitSepClosure_not_isOfFinOrder Ω))
    change E.qUnitSepClosure Ω ^ (c * (n : ℤ)) = E.qUnitSepClosure Ω ^ (0 : ℤ)
    rw [zpow_mul, zpow_natCast, hc, div_pow, hx, hy]
    simp
  have hc' : c = 0 := (mul_eq_zero.mp hc0).resolve_right (by omega)
  rw [hc', zpow_zero] at hc
  exact div_eq_one.mp hc.symm

/-- Normalized solutions of the Kummer equations for a unit parameter. -/
def TateKummerPoint (n : ℕ) (u : Ωˣ) :=
  {ix : Fin n × Ωˣ // ix.2 ^ n = u ^ ix.1.val}

variable {n : ℕ} (b u : Ωˣ) (hq : E.qUnitSepClosure Ω = b ^ n * u)

include hq

omit [DecidableEq Ω] [Algebra.IsAlgebraic K Ω] in
/-- Rescaling a Kummer root by `b ^ i` gives a normalized Tate torsion representative. -/
theorem kummer_rep_pow (a : TateKummerPoint n u) :
    (a.val.2 * b ^ a.val.1.val) ^ n = E.qUnitSepClosure Ω ^ a.val.1.val := by
  rw [mul_pow, a.property, hq, mul_pow, pow_right_comm b]
  exact mul_comm _ _

/-- The point of Tate torsion defined by a normalized Kummer root. -/
noncomputable def kummerTorsionPoint (a : TateKummerPoint n u) :
    AddSubgroup.torsionBy (E⁄Ω).Point (n : ℤ) :=
  ⟨E.tatePoint Ω (a.val.2 * b ^ a.val.1.val),
    (E.tatePoint_mem_torsionBy_iff Ω _ n).mpr
      ⟨a.val.1.val, by simpa only [zpow_natCast] using E.kummer_rep_pow b u hq a⟩⟩

/-- Every Tate torsion point comes from a unique normalized Kummer root. -/
theorem kummerTorsionPoint_bijective (hn : 0 < n) :
    Function.Bijective (E.kummerTorsionPoint b u hq) := by
  constructor
  · intro a c hac
    obtain ⟨hi, hx⟩ := E.normalized_tate_torsion_rep_injective hn
      (E.kummer_rep_pow b u hq a) (E.kummer_rep_pow b u hq c)
      (congrArg Subtype.val hac)
    apply Subtype.ext
    apply Prod.ext hi
    rw [hi] at hx
    exact mul_right_cancel hx
  · intro P
    obtain ⟨i, y, hy, hypow⟩ := E.exists_normalized_tate_torsion_rep hn P
    have hx : (y / b ^ i.val) ^ n = u ^ i.val := by
      rw [div_pow, hypow, hq, mul_pow, pow_right_comm b]
      exact mul_div_cancel_left _ _
    refine ⟨⟨(i, y / b ^ i.val), hx⟩, ?_⟩
    apply Subtype.ext
    change E.tatePoint Ω ((y / b ^ i.val) * b ^ i.val) = P
    simpa only [div_mul_cancel] using hy

/-- A bijection between normalized Kummer roots and Tate torsion.
Compatibility with the carry law is stated separately below. -/
noncomputable def kummerTorsionEquiv (hn : 0 < n) :
    TateKummerPoint n u ≃ AddSubgroup.torsionBy (E⁄Ω).Point (n : ℤ) :=
  Equiv.ofBijective (E.kummerTorsionPoint b u hq) (E.kummerTorsionPoint_bijective b u hq hn)

/-- The Tate comparison respects the Kummer addition formula, including the carry
factor `u ^ k` when the component indices cross a multiple of `n`. -/
theorem kummerTorsionPoint_add (a c d : TateKummerPoint n u) (k : ℕ)
    (hi : a.val.1.val + c.val.1.val = d.val.1.val + n * k)
    (hx : d.val.2 = a.val.2 * c.val.2 / u ^ k) :
    E.kummerTorsionPoint b u hq d =
      E.kummerTorsionPoint b u hq a + E.kummerTorsionPoint b u hq c := by
  have hr : (d.val.2 * b ^ d.val.1.val) * E.qUnitSepClosure Ω ^ k =
      (a.val.2 * b ^ a.val.1.val) * (c.val.2 * b ^ c.val.1.val) := by
    rw [hx, hq, mul_pow, ← pow_mul]
    calc
      _ = (a.val.2 * c.val.2) * b ^ (d.val.1.val + n * k) := by
        simp [pow_add, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      _ = _ := by rw [← hi, pow_add]; ac_rfl
  have hz : E.tatePoint Ω (E.qUnitSepClosure Ω ^ k) = 0 :=
    (E.tatePoint_eq_zero_iff Ω _).mpr
      (Subgroup.mem_zpowers_iff.mpr ⟨(k : ℤ), by simp⟩)
  apply Subtype.ext
  change E.tatePoint Ω (d.val.2 * b ^ d.val.1.val) =
    E.tatePoint Ω (a.val.2 * b ^ a.val.1.val) +
      E.tatePoint Ω (c.val.2 * b ^ c.val.1.val)
  have h := congrArg (E.tatePoint Ω) hr
  simpa only [E.tatePoint_mul, hz, add_zero] using h

/-- The Tate comparison commutes with Galois action whenever the rescaling factor
is fixed; in particular this applies when `b` comes from the base field. -/
theorem kummerTorsionPoint_galois (σ : Ω ≃ₐ[K] Ω)
    (hb : Units.map σ.toAlgHom.toRingHom.toMonoidHom b = b)
    (a c : TateKummerPoint n u) (hi : c.val.1 = a.val.1)
    (hx : c.val.2 = Units.map σ.toAlgHom.toRingHom.toMonoidHom a.val.2) :
    (E.kummerTorsionPoint b u hq c : (E⁄Ω).Point) =
      Affine.Point.map σ.toAlgHom (E.kummerTorsionPoint b u hq a) := by
  change E.tatePoint Ω (c.val.2 * b ^ c.val.1.val) =
    Affine.Point.map σ.toAlgHom (E.tatePoint Ω (a.val.2 * b ^ a.val.1.val))
  rw [E.tatePoint_galois]
  congr 1
  rw [map_mul, map_pow, hb, hi, hx]

end WeierstrassCurve
