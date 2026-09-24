/-
Copyright (c) 2024 Junyan Xu, David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu, David Kurniadi Angdinata, Kelvin Randder
-/
module

public import Init.Data.Int.DivMod
import Mathlib.Algebra.Group.Int.Even
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
public import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Nat.EvenOddRec
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.NumberTheory.EllipticDivisibilitySequence
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination

/-!
# Finiteness of elliptic-curve torsion

The multiplication formula and its supporting identities are ported from mathlib PR #41197
at revision `f46c499f84960839eac3fdbc517a930f02b3b252`. The existing mathlib sequence
definitions are reused; additional sequence identities live in `FLT.NTorsionAux`.

The last section proves that `ΨSq n` is nonzero in every characteristic: otherwise a root
of the monic `Φ n` polynomial would give a singular representative of the multiple of a
nonsingular point. Finite root sets and finite x-coordinate fibres imply finiteness of torsion.
-/

set_option linter.style.longFile 2500

/-!
Ported from mathlib PR #41197, revision
`f46c499f84960839eac3fdbc517a930f02b3b252`
(https://github.com/leanprover-community/mathlib4/pull/41197).

# Elliptic divisibility sequences

This file defines elliptic divisibility sequences (EDS)
and constructs normalised EDSs from initial terms.

## Mathematical background

Let `R` be a commutative ring. An elliptic sequence is a sequence `W : ℤ → R` satisfying
`W(m + n)W(m - n)W(r)² = W(m + r)W(m - r)W(n)² - W(n + r)W(n - r)W(m)²` for any `m, n, r ∈ ℤ`.
A divisibility sequence is a sequence `W : ℤ → R` satisfying `W(m) ∣ W(n)` for any `m, n ∈ ℤ` such
that `m ∣ n`. An elliptic divisibility sequence is simply a divisibility sequence that is elliptic.

Some examples of EDSs include
* the identity sequence,
* certain terms of Lucas sequences, and
* division polynomials of elliptic curves.

## Main definitions

* `IsEllSequence`: a sequence indexed by integers is an elliptic sequence.
* `IsDivSequence`: a sequence indexed by integers is a divisibility sequence.
* `IsEllDivSequence`: a sequence indexed by integers is an EDS.
* `preNormEDS'`: the auxiliary sequence for a normalised EDS indexed by `ℕ`.
* `preNormEDS`: the auxiliary sequence for a normalised EDS indexed by `ℤ`.
* `auxComplEDS₂`: the 2-complement sequence for a normalised EDS indexed by `ℕ`.
* `normEDS`: the canonical example of a normalised EDS indexed by `ℤ`.
* `auxComplEDS'`: the complement sequence for a normalised EDS indexed by `ℕ`.
* `auxComplEDS`: the complement sequence for a normalised EDS indexed by `ℤ`.

## Main statements

 * `isEllDivSequence_normEDS`: `normEDS` satisfies `IsEllDivSequence`.

## Implementation notes

The normalised EDS `normEDS b c d n` is defined in terms of the auxiliary sequence
`preNormEDS (b ^ 4) c d n`, which are equal when `n` is odd, and which differ by a factor of `b`
when `n` is even. This coincides with the definition in the references since both agree for
`normEDS b c d 2` and for `normEDS b c d 4`, and the correct factors of `b` are removed in
`normEDS b c d (2 * (m + 2) + 1)` and in `normEDS b c d (2 * (m + 3))`.

One reason is to avoid the necessity for ring division by `b` in the inductive definition of
`normEDS b c d (2 * (m + 3))`. The idea is that it can be shown that `normEDS b c d (2 * (m + 3))`
always contains a factor of `b`, so it is possible to remove a factor of `b` *a posteriori*, but
stating this lemma requires first defining `normEDS b c d (2 * (m + 3))`, which requires having this
factor of `b` *a priori*. Another reason is to allow the definition of univariate `n`-division
polynomials of elliptic curves, omitting a factor of the bivariate `2`-division polynomial.

## References

M Ward, *Memoir on Elliptic Divisibility Sequences*

## Tags

elliptic, divisibility, sequence
-/


@[expose] public section

namespace FLT.NTorsionAux

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (W : ℤ → R)
variable {F : Type*} [FunLike F R S] [RingHomClass F R S] (f : F)

open scoped nonZeroDivisors

namespace EllSequence

/-- The expression `W((m+n)/2) * W((m-n)/2)` is the basic building block of elliptic relations,
where integers `m` and `n` should have the same parity. -/
def addMulSub (m n : ℤ) : R := W ((m + n).tdiv 2) * W ((m - n).tdiv 2)
-- Implementation note: we use `Int.tdiv _ 2` instead of `_ / 2` so that
-- `(-m).tdiv 2 = -(m.tdiv 2)`
-- and lemmas like `addMulSub_neg₀` hold unconditionally, even though in the case we care about
-- (`m` and `n` both even or both odd) both are equal.

/-- The four-index elliptic relation, defined in terms of `addMulSub`,
featuring the three partitions of four indices into two pairs.
Intended to apply to four integers of the same parity. -/
def rel₄ (a b c d : ℤ) : R :=
  addMulSub W a b * addMulSub W c d
    - addMulSub W a c * addMulSub W b d + addMulSub W a d * addMulSub W b c

/-- The defining property of Stange's elliptic nets,
equivalent to a suitable valid (same-parity indices) `rel₄` relation,
but here only the first three indices enjoy symmetry under permutation,
while in `rel₄` all four indices can be freely permuted.

The order of the last two terms are changed and two signs are swapped compared to Stange's
paper to make the equivalence with elliptic relations unconditional (indepedent of W
being an odd function). This should also avoid peculiarities in characterstic 3. -/
def net (p q r s : ℤ) : R :=
  W (p + q + s) * W (p - q) * W (r + s) * W r
    - W (p + r + s) * W (p - r) * W (q + s) * W q
    + W (q + r + s) * W (q - r) * W (p + s) * W p

variable {W} in
lemma net_eq_rel₄ {p q r s : ℤ} :
    net W p q r s = rel₄ W (2 * p + s) (2 * q + s) (2 * r + s) s := by
  simp_rw [net, rel₄, addMulSub, add_add_add_comm _ s, add_sub_add_comm, sub_self, add_zero,
    add_assoc, ← two_mul, add_sub_cancel_right, ← left_distrib, ← mul_sub_left_distrib,
    Int.mul_tdiv_cancel_left _ two_ne_zero]
  ring

/-- The three-index elliptic relation, obtained by
specializing to `d = 0` in the four-index relation. -/
def Rel₃ (m n r : ℤ) : Prop :=
  W (m + n) * W (m - n) * W r ^ 2 =
    W (m + r) * W (m - r) * W n ^ 2 - W (n + r) * W (n - r) * W m ^ 2

/-- The proposition that a sequence indexed by integers is an elliptic sequence. -/
def _root_.FLT.NTorsionAux.IsEllSequence : Prop :=
  ∀ m n r : ℤ, Rel₃ W m n r

/-- The numerator of an invariant of an elliptic sequence, such that for each `s`,
`invarNum s n / invarDenom s n` is a constant independent of `n`. -/
def invarNum (s n : ℤ) : R :=
  (W (n + 2 * s) * W (n - s) ^ 2 + W (n + s) ^ 2 * W (n - 2 * s)) * W s ^ 2
    + W n ^ 3 * W (2 * s) ^ 2

/-- The denominator of an invariant of an elliptic sequence. -/
def invarDenom (s n : ℤ) : R := W (n + s) * W n * W (n - s)

set_option allowUnsafeReducibility true in
attribute [local reducible] Nat.rawCast Mathlib.Meta.NormNum.instAddMonoidWithOne in
theorem invar_of_net (net_eq_zero : ∀ p q r s, net W p q r s = 0) (s m n : ℤ) :
    invarNum W s m * invarDenom W s n = invarNum W s n * invarDenom W s m := by
  simp_rw [invarNum, invarDenom]
  linear_combination (norm := (simp_rw [net]; ring_nf))
    net_eq_zero m n s 0 * W m * W n * W (2 * s) ^ 2
      - (net_eq_zero m n s s * W (m - s) * W (n - s)
        + net_eq_zero (m - s) (n - s) s s * W (m + s) * W (n + s)
        - net_eq_zero (n + s) n (n - s) (m - n) * W (m - n) * W (2 * s)) * W s ^ 2

lemma net_add_sub_iff (m n : ℤ) :
    net W (m + n) m (m - n) n = 0 ↔
      W (2 * (m + n)) * W (m - n) * W m * W n =
        (W (2 * m + n) * W (2 * n) * W m - W (m + 2 * n) * W (2 * m) * W n) * W (m + n) := by
  simp_rw [net, show m + n + m + n = 2 * (m + n) by ring,
    show m + n - m = n by ring, show m - n + n = m by ring,
    show m + n + (m - n) + n = 2 * m + n by ring,
    show m + n - (m - n) = 2 * n by ring,
    show m + (m - n) + n = 2 * m by ring,
    show m - (m - n) = n by ring, show m + n + n = m + 2 * n by ring]
  constructor <;> intro h <;> linear_combination h

lemma addMulSub_two_zero : addMulSub W 2 0 = W 1 ^ 2 := (sq _).symm
lemma addMulSub_three_one : addMulSub W 3 1 = W 2 * W 1 := rfl

lemma addMulSub_even (m n : ℤ) : addMulSub W (2 * m) (2 * n) = W (m + n) * W (m - n) := by
  simp_rw [addMulSub, ← left_distrib, ← mul_sub_left_distrib,
    Int.mul_tdiv_cancel_left _ two_ne_zero]

lemma addMulSub_odd (m n : ℤ) :
    addMulSub W (2 * m + 1) (2 * n + 1) = W (m + n + 1) * W (m - n) := by
  have h k := Int.mul_tdiv_cancel_left k two_ne_zero
  rw [addMulSub, ← h (m + n + 1), ← h (m - n)]; congr <;> ring

lemma addMulSub_same (zero : W 0 = 0) (m : ℤ) : addMulSub W m m = 0 := by
  rw [addMulSub, sub_self, Int.zero_tdiv, zero, mul_zero]

lemma addMulSub_neg₀ (neg : ∀ k, W (-k) = -W k) (m n : ℤ) :
    addMulSub W (-m) n = addMulSub W m n := by
  simp_rw [addMulSub, ← neg_add', neg_add_eq_sub, ← neg_sub m, Int.neg_tdiv, neg]; ring

lemma addMulSub_neg₁ (m n : ℤ) : addMulSub W m (-n) = addMulSub W m n := by
  rw [addMulSub, addMulSub, mul_comm]; abel_nf

lemma addMulSub_abs₀ (neg : ∀ k, W (-k) = -W k) (m n : ℤ) :
    addMulSub W |m| n = addMulSub W m n := by
  obtain h | h := abs_choice m <;> simp only [h, addMulSub_neg₀ W neg]

lemma addMulSub_abs₁ (m n : ℤ) : addMulSub W m |n| = addMulSub W m n := by
  obtain h | h := abs_choice n <;> simp only [h, addMulSub_neg₁]

lemma addMulSub_swap (neg : ∀ k, W (-k) = -W k) (m n : ℤ) :
    addMulSub W m n = - addMulSub W n m := by
  rw [addMulSub, addMulSub, ← neg_sub, Int.neg_tdiv, neg]; ring_nf

section transf

variable (a b c d : ℤ)

/-- The proposition that the four indices are all nonnegative and strictly decreasing. -/
def StrictAnti₄ : Prop := 0 ≤ d ∧ d < c ∧ c < b ∧ b < a

/-- The proposition that the four indices are of the same parity. -/
def HaveSameParity₄ : Prop :=
  a.negOnePow = b.negOnePow ∧ b.negOnePow = c.negOnePow ∧ c.negOnePow = d.negOnePow

/-- The average of four indices. -/
def avg₄ : ℤ := (a + b + c + d) / 2

namespace HaveSameParity₄
open Int Equiv

variable {W a b c d} (same : HaveSameParity₄ a b c d)
include same

lemma rel₄_eq_net : rel₄ W a b c d = net W ((a - d) / 2) ((b - d) / 2) ((c - d) / 2) d := by
  have h := @Int.two_mul_ediv_two_of_even
  rw [net_eq_rel₄, h, h, h]; · simp_rw [sub_add_cancel]
  all_goals rw [← negOnePow_eq_iff]
  exacts [same.2.2, same.2.1.trans same.2.2, same.1.trans (same.2.1.trans same.2.2)]

lemma even_sum : Even (a + b + c + d) := by
  simp_rw [← negOnePow_eq_one_iff, negOnePow_add,
    same.1, same.2.1, same.2.2, units_mul_self, one_mul, units_mul_self]

lemma avg₄_add_avg₄ : avg₄ a b c d + avg₄ a b c d = a + b + c + d := by
  rw [← two_mul]; exact Int.mul_ediv_cancel' same.even_sum.two_dvd

lemma same₀₃ : a.negOnePow = d.negOnePow := by rw [same.1, same.2.1, same.2.2]

protected lemma abs : HaveSameParity₄ |a| |b| |c| |d| := by
  simpa only [HaveSameParity₄, negOnePow_abs] using same

omit same in
lemma perm (σ : Perm (Fin 4)) :
    ∀ t : Fin 4 → ℤ, HaveSameParity₄ (t 0) (t 1) (t 2) (t 3) →
      HaveSameParity₄ (t (σ 0)) (t (σ 1)) (t (σ 2)) (t (σ 3)) := by
  have hmem := (Perm.mclosure_swap_castSucc_succ 3).symm ▸ Submonoid.mem_top σ
  refine Submonoid.closure_induction
    (motive := fun σ _ ↦ ∀ t : Fin 4 → ℤ, HaveSameParity₄ (t 0) (t 1) (t 2) (t 3) →
      HaveSameParity₄ (t (σ 0)) (t (σ 1)) (t (σ 2)) (t (σ 3)))
    ?_ (fun _ ↦ id) (fun σ τ _ _ hσ hτ t same ↦ ?_) hmem
  on_goal 2 => simp_rw [Perm.mul_apply]; exact hτ (t ∘ σ) (hσ _ same)
  rintro _ ⟨i, rfl⟩ t ⟨h₀₁, h₁₂, h₂₃⟩; fin_cases i
  exacts [⟨h₀₁.symm, h₀₁ ▸ h₁₂, h₂₃⟩, ⟨h₀₁ ▸ h₁₂, h₁₂.symm, h₁₂ ▸ h₂₃⟩, ⟨h₀₁, h₁₂ ▸ h₂₃, h₂₃.symm⟩]

lemma six_le_of_strictAnti₄ (anti : StrictAnti₄ a b c d) : 6 ≤ a := by
  simp_rw [HaveSameParity₄, negOnePow_eq_iff] at same
  obtain ⟨hd, hdc, hcb, hba⟩ := anti
  rw [← add_two_le_iff_lt_of_even_sub] at hdc hcb hba
  · linarith
  exacts [same.1, same.2.1, same.2.2]

variable (W) in
/-- A hybrid product formed by one factor from an `addMulSub` and one from another `addMulSub`. -/
def addMulSub₄ (a b c d : ℤ) : R := W ((a + b).tdiv 2) * W ((c - d).tdiv 2)

omit same in
lemma addMulSub₄_mul_addMulSub₄ :
    addMulSub₄ W a b c d * addMulSub₄ W c d a b = addMulSub W a b * addMulSub W c d := by
  simp_rw [addMulSub₄, addMulSub]; ring

set_option allowUnsafeReducibility true in
attribute [local reducible] Nat.rawCast Mathlib.Meta.NormNum.instAddMonoidWithOne in
lemma addMulSub_transf :
    addMulSub W (avg₄ a b c d - d) (avg₄ a b c d - c) = addMulSub₄ W a b c d ∧
      addMulSub W (avg₄ a b c d - d) (avg₄ a b c d - b) = addMulSub₄ W a c b d ∧
      addMulSub W (avg₄ a b c d - d) |avg₄ a b c d - a| = addMulSub₄ W b c a d ∧
      addMulSub W (avg₄ a b c d - c) (avg₄ a b c d - b) = addMulSub₄ W a d b c ∧
      addMulSub W (avg₄ a b c d - c) |avg₄ a b c d - a| = addMulSub₄ W b d a c ∧
      addMulSub W (avg₄ a b c d - b) |avg₄ a b c d - a| = addMulSub₄ W c d a b := by
  simp_rw [addMulSub_abs₁, addMulSub, addMulSub₄, sub_add_sub_comm, same.avg₄_add_avg₄]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring_nf

theorem rel₄_transf :
    rel₄ W (avg₄ a b c d - d) (avg₄ a b c d - c) (avg₄ a b c d - b) |avg₄ a b c d - a| =
      rel₄ W a b c d := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := same.addMulSub_transf (W := W)
  simp_rw [rel₄, h₁, h₂, h₃, h₄, h₅, h₆, addMulSub₄_mul_addMulSub₄]; ring

theorem transf : HaveSameParity₄
    (avg₄ a b c d - d) (avg₄ a b c d - c) (avg₄ a b c d - b) |avg₄ a b c d - a| := by
  simp_rw [HaveSameParity₄, negOnePow_abs, negOnePow_sub, same.1, same.2.1, same.2.2, true_and]

theorem strictAnti₄_transf (anti : StrictAnti₄ a b c d) :
    StrictAnti₄ (avg₄ a b c d - d) (avg₄ a b c d - c) (avg₄ a b c d - b) |avg₄ a b c d - a| := by
  obtain ⟨hd, hdc, hcb, hba⟩ := anti
  refine ⟨abs_nonneg _, abs_lt.mpr ⟨?_, ?_⟩, ?_, ?_⟩ <;> rw [← sub_pos]
  · rw [sub_neg_eq_add, sub_add_sub_comm, same.avg₄_add_avg₄]; linarith only [hd, hdc]
  all_goals linarith only [hdc, hcb, hba]

end HaveSameParity₄

end transf

/-- The four-index elliptic relation multiplied by a two-index "coefficient". -/
abbrev rel₆ (k l a b c d : ℤ) : R := addMulSub W k l * rel₄ W a b c d

@[simp] lemma rel₆_eq (k l a b c d : ℤ) :
    rel₆ W k l a b c d = addMulSub W k l * rel₄ W a b c d := rfl

lemma rel₃_iff₄ (m n r : ℤ) :
    Rel₃ W m n r ↔ rel₄ W (2 * m) (2 * n) (2 * r) 0 = 0 := by
  rw [rel₄, ← mul_zero 2, Rel₃]
  simp_rw [addMulSub_even, add_zero, sub_zero]
  convert sub_eq_zero.symm using 2; ring

/-! In the following three key lemmas we use `m`, `n`, `r`, `s` to denote "free" indices and
`c`, `d` to denote "fixed" indices. -/

/-- A `rel₄` with a fixed index and three free indices can be expressed in terms of
three `rel₄`s with two fixed indices and two free indices that share one fixed index
(the larger one) and two free indices with the first `rel₄`.
The coefficient before the first `rel₄` is `addMulSub` applied to the two fixed indices. -/
lemma rel₆_eq₃ (c d m n r : ℤ) :
    rel₆ W c d m n r c = rel₆ W m c n r c d - rel₆ W n c m r c d + rel₆ W r c m n c d := by
  simp_rw [rel₆, rel₄]; ring

/-- A `rel₄` with a fixed index and three free indices can be expressed in terms of
three `rel₄`s with two fixed indices and two free indices that share one fixed index
(the smaller one) and two free indices with the first `rel₄`.
The coefficient before the first `rel₄` is `addMulSub` applied to the two fixed indices. -/
lemma rel₆_eq₃' (c d m n r : ℤ) :
    rel₆ W c d m n r d = rel₆ W m d n r c d - rel₆ W n d m r c d + rel₆ W r d m n c d := by
  simp_rw [rel₆, rel₄]; ring

/-- A `rel₄` with four free indices can be expressed in terms of ten `rel₄`s
with at least one index chosen from two possibilities (fixed indices) and
the other indices chosen from the indices of the first `rel₄`.
The coefficient before the first `rel₄` is `addMulSub` applied to the two fixed indices. -/
theorem rel₆_eq₁₀ (c d m n r s : ℤ) :
    rel₆ W c d m n r s =
      rel₆ W n d m r s c - rel₆ W r d m n s c + rel₆ W s d m n r c
      + rel₆ W n c m r s d - rel₆ W r c m n s d + rel₆ W s c m n r d
      + rel₆ W n r m s c d - rel₆ W n s m r c d + rel₆ W r s m n c d
      - 2 * rel₆ W m d n r s c := by
  simp_rw [rel₆, rel₄]; ring

theorem addMulSub_sq_mul_rel₄_eq₉ (c d m n r s : ℤ) :
    (addMulSub W c d) ^ 2 * rel₄ W m n r s =
      addMulSub W m c * (rel₆ W n d r s c d - rel₆ W r d n s c d + rel₆ W s d n r c d)
                    -- = rel₆ W c d n r s d ↑ by rel₆_eq₃'   = rel₆ W c d n r s c ↓ by rel₆_eq₃
      - addMulSub W m d * (rel₆ W n c r s c d - rel₆ W r c n s c d + rel₆ W s c n r c d)
      + addMulSub W c d * (rel₆ W n r m s c d - rel₆ W n s m r c d + rel₆ W r s m n c d) := by
                         -- the third row in RHS of rel₆_eq₁₀
  simp_rw [rel₆, rel₄]; ring

/-- The recurrence defining odd terms of an elliptic sequence,
a particular case of the elliptic relation according to `rel₃_iff_oddRec`. -/
def OddRec (m : ℤ) : Prop :=
  W (2 * m + 1) * W 1 ^ 3 = W (m + 2) * W m ^ 3 - W (m - 1) * W (m + 1) ^ 3

/-- The recurrence defining even terms of an elliptic sequence, a particular case
of the elliptic relation according to `rel₃_iff_evenRec` and `rel₄_iff_evenRec`. -/
def EvenRec (m : ℤ) : Prop :=
  W (2 * m) * W 2 * W 1 ^ 2 = W m * (W (m - 1) ^ 2 * W (m + 2) - W (m - 2) * W (m + 1) ^ 2)

lemma rel₃_iff_oddRec (m : ℤ) : Rel₃ W (m + 1) m 1 ↔ OddRec W m := by
  rw [Rel₃, OddRec]; ring_nf

set_option allowUnsafeReducibility true in
attribute [local reducible] Nat.rawCast Mathlib.Meta.NormNum.instAddMonoidWithOne in
lemma rel₃_iff_evenRec (m : ℤ) : Rel₃ W (m + 1) (m - 1) 1 ↔ EvenRec W m := by
  rw [Rel₃, EvenRec]; ring_nf

set_option allowUnsafeReducibility true in
attribute [local reducible] Nat.rawCast Mathlib.Meta.NormNum.instAddMonoidWithOne in
lemma rel₄_iff_evenRec (m : ℤ) : rel₄ W (2 * m + 1) (2 * m - 1) 3 1 = 0 ↔ EvenRec W m := by
  have hr : rel₄ W (2 * m + 1) (2 * m - 1) 3 1
      = rel₄ W (2 * m + 1) (2 * (m - 1) + 1) (2 * 1 + 1) (2 * 0 + 1) := by
    congr 1; ring
  rw [iff_comm, EvenRec, ← sub_eq_zero, hr, rel₄, addMulSub_odd, addMulSub_odd,
    addMulSub_odd, addMulSub_odd, addMulSub_odd, addMulSub_odd]
  ring_nf

/-- The minimal possible fourth index in the four-index elliptic relation given the first index. -/
def dMin (a : ℤ) : ℤ := if Even a then 0 else 1
/-- The minimal possible third index in the four-index elliptic relation given the first index. -/
def cMin (a : ℤ) : ℤ := dMin a + 2

lemma dMin_nonneg (a : ℤ) : 0 ≤ dMin a := by rw [dMin]; split_ifs <;> decide

lemma dMin_lt_cMin (a : ℤ) : dMin a < cMin a := lt_add_of_pos_right _ zero_lt_two

lemma negOnePow_cMin_eq_dMin (a : ℤ) : (cMin a).negOnePow = (dMin a).negOnePow := by
  rw [cMin, Int.negOnePow_add]; exact mul_one _

lemma negOnePow_dMin (a : ℤ) : (dMin a).negOnePow = a.negOnePow := by
  rw [dMin]; split_ifs with h
  · simp [Int.negOnePow_even, h]
  · simp [Int.negOnePow_odd, Int.not_even_iff_odd.mp h]

lemma negOnePow_cMin (a : ℤ) : (cMin a).negOnePow = a.negOnePow := by
  rw [negOnePow_cMin_eq_dMin, negOnePow_dMin]

variable {W}
lemma addMulSub_mem_nonZeroDivisors (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰) (a : ℤ) :
    addMulSub W (cMin a) (dMin a) ∈ R⁰ := by
  rw [cMin, dMin]; split_ifs; exacts [mul_mem one one, mul_mem two one]

lemma dMin_le {a b : ℤ} (same : a.negOnePow = b.negOnePow) (h : 0 ≤ b) : dMin a ≤ b := by
  rw [dMin]; split_ifs with odd
  exacts [h, h.lt_of_ne (by rintro rfl; exact odd (a.negOnePow_eq_one_iff.mp same))]

open Int

section Rel₄OfValid

variable (W) in
/-- The four-index elliptic relation restricted to the case where the four indices are
nonnegative, have the same parity and are strictly decreasing. -/
def Rel₄OfValid (a b c d : ℤ) : Prop :=
  HaveSameParity₄ a b c d → StrictAnti₄ a b c d → rel₄ W a b c d = 0

variable {a c₀ d₀ : ℤ} (par : c₀.negOnePow = d₀.negOnePow) (le : 0 ≤ d₀) (lt : d₀ < c₀)
  (rel : ∀ {a' b}, a' ≤ a → Rel₄OfValid W a' b c₀ d₀) (mem : addMulSub W c₀ d₀ ∈ R⁰)
include par le lt rel mem

/-- If `rel₄` holds for all quadruples of the form `(a', b, c₀, d₀)` for arbitrary `b` and
`a' < a`, then it holds for `(a, b, c, c₀)` and `(a, b, c, d₀)` for arbitrary `b` and `c`
(subject to some technical conditions). -/
lemma rel₄_fix₁_of_fix₂ (b c : ℤ) :
    Rel₄OfValid W a b c c₀ ∧ (c₀ < c → Rel₄OfValid W a b c d₀) := by
  refine ⟨fun same anti ↦ mem.2 _ ?_, fun _hc same anti ↦ mem.2 _ ?_⟩ <;> rw [mul_comm, ← rel₆_eq]
  on_goal 1 => rw [rel₆_eq₃]; have _hc := trivial
  on_goal 2 => rw [rel₆_eq₃']
  all_goals simp only [rel₆_eq]; rw [rel le_rfl, rel le_rfl, rel anti.2.2.2.le]
  iterate 2
    simp_rw [mul_zero, add_zero, sub_zero]
    iterate 3
      simp only [HaveSameParity₄, par, same.1, same.2.1, same.2.2, true_and]
      refine ⟨le, lt, ?_, ?_⟩ <;> linarith only [_hc, anti.2.1, anti.2.2.1, anti.2.2.2]

/-- If `rel₄` holds for all quadruples of the form `(a', b, c₀, d₀)` for arbitrary `b` and
`a' < a`, then it holds for `(a, b, c, d)` for arbitrary `b`, `c` and `d`
(subject to some technical conditions). -/
lemma rel₄_of_fix₂ (b c d : ℤ) (hc : c₀ < d) (par' : d.negOnePow = d₀.negOnePow) :
    Rel₄OfValid W a b c d := fun same ⟨_, hdc, hcb, hba⟩ ↦ mem.2 _ <| by
  rw [mul_comm, ← rel₆_eq, rel₆_eq₁₀]; simp only [rel₆_eq]
  have fix₁ b c := (rel₄_fix₁_of_fix₂ par le lt rel mem b c).1
  have fix₂ {b c} := (rel₄_fix₁_of_fix₂ par le lt rel mem b c).2
  rw [fix₁, fix₁, fix₁, fix₂ hc, fix₂ hc, fix₂ (hc.trans hdc), rel le_rfl, rel le_rfl,
    rel le_rfl, (rel₄_fix₁_of_fix₂ par le lt (fun h ↦ rel <| h.trans hba.le) mem _ _).1]
  · simp_rw [mul_zero, add_zero, sub_zero]
  iterate 10
    simp only [HaveSameParity₄, par, par', same.1, same.2.1, same.2.2, true_and]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith only [hc, le, lt, hdc, hcb, hba]

omit par le lt rel mem in
/-- Specialize previous lemmas to the case `c₀ = cMin a` and `d₀ = dMin a`,
and combine them to remove technical conditions about the relative order of the indices. -/
theorem rel₄_of_min₂ (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
    (rel : ∀ {a' b}, a' ≤ a → Rel₄OfValid W a' b (cMin a) (dMin a)) (b c d : ℤ) :
    Rel₄OfValid W a b c d := fun same anti ↦ by
  obtain hc|hc := lt_or_ge (cMin a) d
  · refine rel₄_of_fix₂ (negOnePow_cMin_eq_dMin a) (dMin_nonneg a) (dMin_lt_cMin a) rel
      (addMulSub_mem_nonZeroDivisors one two a) _ _ _ hc ?_ same anti
    rw [negOnePow_dMin, same.1, same.2.1, same.2.2]
  have fix := rel₄_fix₁_of_fix₂ (negOnePow_cMin_eq_dMin a) (dMin_nonneg a) (dMin_lt_cMin a) rel
    (addMulSub_mem_nonZeroDivisors one two a) b c
  obtain rfl|hc := hc.eq_or_lt
  · exact fix.1 same anti
  obtain rfl : dMin a = d := (dMin_le same.same₀₃ anti.1).antisymm <| by
    rwa [← add_two_le_iff_lt_of_even_sub, cMin, add_le_add_iff_right] at hc
    rw [← negOnePow_eq_iff, negOnePow_cMin, same.same₀₃]
  obtain rfl|hc : cMin a = c ∨ _ := ((add_two_le_iff_lt_of_even_sub <| by
    rw [← negOnePow_eq_iff, negOnePow_dMin, same.1, same.2.1]).mpr anti.2.1).eq_or_lt
  exacts [rel le_rfl same anti, fix.2 hc same anti]

omit par le lt rel mem in
-- The main inductive argument.
theorem rel₄_of_anti_oddRec_evenRec (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
    (oddRec : ∀ m ≥ 2, OddRec W m) (evenRec : ∀ m ≥ 3, EvenRec W m) :
    ∀ ⦃a b c d : ℤ⦄, Rel₄OfValid W a b c d :=
  -- apply induction on `a`
  Int.strongRec (m := 6) -- if `a < 6` the conclusion holds vacuously
    (fun a ha b c d same anti ↦ absurd ha (not_lt.mpr (same.six_le_of_strictAnti₄ anti)))
    -- otherwise, it suffices to deal with the "minimal" case `c = cMin a` and `d = dMin a`
    fun a h6 ih ↦ rel₄_of_min₂ one two fun {a' b} haa same anti ↦ by
  obtain ha'|ha' := lt_or_eq_of_le haa
  · -- if a' < a, apply the inductive hypothesis
    exact ih _ ha' same anti
  obtain hba|rfl := lt_or_eq_of_le <| show b + 2 ≤ a' from
    (add_two_le_iff_lt_of_even_sub <| (negOnePow_eq_iff _ _).1 same.1).mpr anti.2.2.2
  · -- if b + 2 < a', apply `transf` and then the inductive hypothesis is applicable
    rw [← same.rel₄_transf]
    refine ih _ ?_ same.transf (same.strictAnti₄_transf anti)
    rw [avg₄, sub_lt_iff_lt_add, Int.ediv_lt_iff_lt_mul zero_lt_two, ← ha', cMin]
    linarith only [hba]
  obtain ⟨m, rfl|rfl⟩ := b.even_or_odd'
  -- the b + 2 = a' case is handled by oddRec or evenRec depending on the parity of `b`
  · have ea : Even a := by rw [← ha']; exact (even_two_mul _).add even_two
    simp_rw [cMin, dMin, ite_eq_left ea]
    convert (rel₃_iff₄ W (m + 1) m 1).mp
      ((rel₃_iff_oddRec W m).mpr <| oddRec _ (by linarith only [h6, ha'])) using 2 <;> ring
  · have nea : ¬ Even a := by
      rw [← ha', not_even_iff_odd]; convert odd_two_mul_add_one (m + 1) using 1; ring
    simp_rw [cMin, dMin, ite_eq_right nea]
    convert (rel₄_iff_evenRec W (m + 1)).mpr
      (evenRec _ (by linarith only [h6, ha'])) using 2 <;> ring

end Rel₄OfValid

section Perm

variable (neg : ∀ k, W (-k) = -W k)
include neg

lemma rel₄_abs {m n r s : ℤ} : rel₄ W |m| |n| |r| |s| = rel₄ W m n r s := by
  simp_rw [rel₄, addMulSub_abs₀ W neg, addMulSub_abs₁]

lemma rel₄_swap₀₁ {m n r s : ℤ} : rel₄ W m n r s = - rel₄ W n m r s := by
  simp_rw [rel₄, addMulSub_swap W neg n m]; ring

lemma rel₄_swap₁₂ {m n r s : ℤ} : rel₄ W m n r s = - rel₄ W m r n s := by
  simp_rw [rel₄, addMulSub_swap W neg r n]; ring

lemma rel₄_swap₂₃ {m n r s : ℤ} : rel₄ W m n r s = - rel₄ W m n s r := by
  simp_rw [rel₄, addMulSub_swap W neg s r]; ring

open Equiv

variable (W) in
/-- The four-index elliptic relation with a tuple as input. -/
def relFin4 (t : Fin 4 → ℤ) : R := rel₄ W (t 0) (t 1) (t 2) (t 3)

/-- `rel₄` is invariant (up to sign) under permutation of the four indices. -/
theorem relFin4_perm (σ : Perm (Fin 4)) : ∀ t, relFin4 W (t ∘ σ) = Perm.sign σ • relFin4 W t := by
  have hmem := (Perm.mclosure_swap_castSucc_succ 3).symm ▸ Submonoid.mem_top σ
  refine Submonoid.closure_induction
    (motive := fun (σ : Perm (Fin 4)) _ ↦ ∀ t, relFin4 W (t ∘ σ) = Perm.sign σ • relFin4 W t)
    ?_ (fun t ↦ by simp) (fun σ τ _ _ hσ hτ t ↦ ?_) hmem
  on_goal 2 =>
    rw [Perm.coe_mul, ← Function.comp_assoc, hτ, hσ, map_mul, mul_comm, mul_smul]
  rintro _ ⟨i, rfl⟩ t; fin_cases i <;>
    rw [Perm.sign_swap Fin.castSucc_lt_succ.ne, Units.neg_smul, one_smul]
  exacts [rel₄_swap₀₁ neg, rel₄_swap₁₂ neg, rel₄_swap₂₃ neg]

lemma relFin4_perm' (σ : Perm (Fin 4)) (t) : Perm.sign σ • relFin4 W (t ∘ σ) = relFin4 W t := by
  rw [relFin4_perm neg, ← mul_smul, Int.units_mul_self, one_smul]

variable (zero : W 0 = 0)
include zero

/-! `rel₄` is trivial when two indices are equal. -/

omit neg in
lemma rel₄_same₀₁ (m r s : ℤ) : rel₄ W m m r s = 0 := by
  simp_rw [rel₄, addMulSub_same W zero]; ring

omit neg in
lemma rel₄_same₁₂ (m n s : ℤ) : rel₄ W m n n s = 0 := by
  simp_rw [rel₄, addMulSub_same W zero]; ring

omit neg in
lemma rel₄_same₂₃ (m n r : ℤ) : rel₄ W m n r r = 0 := by
  simp_rw [rel₄, addMulSub_same W zero]; ring

variable (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
  (oddRec : ∀ m ≥ 2, OddRec W m) (evenRec : ∀ m ≥ 3, EvenRec W m)
include one two oddRec evenRec

/-- The four-index `rel₄` relations follow from
the single-index `oddRec` and `evenRec` recursive relations. -/
theorem rel₄_of_oddRec_evenRec {a b c d : ℤ} (same : HaveSameParity₄ a b c d) :
    rel₄ W a b c d = 0 := by
  let t := ![|a|, |b|, |c|, |d|]
  have nonneg i : 0 ≤ t i := by fin_cases i <;> exact abs_nonneg _
  let σ := Fin.revPerm.trans (Tuple.sort t)
  have anti : Antitone (t ∘ σ) := by
    simp_rw [σ, coe_trans, ← Function.comp_assoc]
    exact (Tuple.monotone_sort t).comp_antitone fun _ _ ↦ Fin.rev_le_rev.mpr
  clear_value σ -- otherwise, unifying `t (σ i)` with `(t ∘ σ) i` is extremely slow
  rw [← rel₄_abs neg]; change relFin4 W t = 0
  rw [← relFin4_perm' neg σ, relFin4]; simp_rw [Function.comp]
  by_cases h₃₂ : t (σ 3) = t (σ 2); · rw [h₃₂, rel₄_same₂₃ zero, smul_zero]
  by_cases h₂₁ : t (σ 2) = t (σ 1); · rw [h₂₁, rel₄_same₁₂ zero, smul_zero]
  by_cases h₁₀ : t (σ 1) = t (σ 0); · rw [h₁₀, rel₄_same₀₁ zero, smul_zero]
  rw [rel₄_of_anti_oddRec_evenRec one two oddRec evenRec (same.abs.perm _ _), smul_zero]
  exact ⟨nonneg _, (anti <| by decide).lt_of_ne h₃₂,
    (anti <| by decide).lt_of_ne h₂₁, (anti <| by decide).lt_of_ne h₁₀⟩

/-- An ℕ-indexed sequence satisfying the even-odd recurrence, after extension to all integers
by symmetry (to make an odd function), is an elliptic sequence, provided its first two terms
are not zero divisors. -/
theorem _root_.FLT.NTorsionAux.IsEllSequence.of_oddRec_evenRec : IsEllSequence W := fun m n r ↦ by
  rw [rel₃_iff₄, rel₄_of_oddRec_evenRec neg zero one two oddRec evenRec]
  refine ⟨?_, ?_, ?_⟩ <;> simp only [negOnePow_two_mul, negOnePow_zero]

end Perm

end EllSequence

open EllSequence

/-- The proposition that a sequence indexed by integers is a divisibility sequence. -/
def IsDivSequence : Prop :=
  ∀ m n : ℤ, m ∣ n → W m ∣ W n

/-- The proposition that a sequence indexed by integers is an EDS. -/
def IsEllDivSequence : Prop :=
  IsEllSequence W ∧ IsDivSequence W

lemma isEllSequence_id : IsEllSequence id :=
  fun _ _ _ ↦ by simp only [Rel₃, id_eq]; ring1

lemma isDivSequence_id : IsDivSequence id :=
  fun _ _ ↦ id

/-- The identity sequence is an EDS. -/
theorem isEllDivSequence_id : IsEllDivSequence id :=
  ⟨isEllSequence_id, isDivSequence_id⟩

variable {W}

lemma IsEllSequence.smul (h : IsEllSequence W) (x : R) : IsEllSequence (x • W) :=
  fun m n r ↦ by
    have key := h m n r
    change Rel₃ (x • W) m n r
    simp only [Rel₃, Pi.smul_apply, smul_eq_mul] at key ⊢
    linear_combination (norm := ring) x ^ 4 * key

lemma IsDivSequence.smul (h : IsDivSequence W) (x : R) : IsDivSequence (x • W) :=
  (mul_dvd_mul_left x <| h · · ·)

lemma IsEllDivSequence.smul (h : IsEllDivSequence W) (x : R) : IsEllDivSequence (x • W) :=
  ⟨h.left.smul x, h.right.smul x⟩

lemma IsEllSequence.map (h : IsEllSequence W) : IsEllSequence (f ∘ W) := fun m n r ↦ by
  simpa only [Rel₃, Function.comp_apply, map_mul, map_pow, map_sub] using congr_arg f (h m n r)

lemma IsDivSequence.map (h : IsDivSequence W) : IsDivSequence (f ∘ W) :=
  (map_dvd f <| h · · ·)

lemma IsEllDivSequence.map (h : IsEllDivSequence W) : IsEllDivSequence (f ∘ W) :=
  ⟨h.1.map f, h.2.map f⟩

namespace IsEllSequence

open EllSequence

variable (ell : IsEllSequence W)
include ell

lemma oddRec (m : ℤ) : OddRec W m := (rel₃_iff_oddRec W m).mp (ell _ _ _)
lemma evenRec (m : ℤ) : EvenRec W m := (rel₃_iff_evenRec W m).mp (ell _ _ _)

lemma zero' [IsReduced R] : W 0 = 0 := by
  have := ell 0 0 0
  simp_rw [Rel₃, add_zero, sub_self, mul_assoc, ← pow_succ'] at this
  exact IsReduced.eq_zero _ ⟨_, this⟩

/-- The zeroth term of an elliptic sequence is zero,
provided some even term is not a zero divisor. -/
lemma zero (m : ℤ) (mem : W (2 * m) ∈ R⁰) : W 0 = 0 := by
  have := ell m m (2 * m)
  rw [Rel₃, add_comm, sub_self, sub_self, ← two_mul, mul_comm (W _)] at this
  exact mem.2 _ ((pow_mem mem 2).2 (W 0 * W (2 * m)) this)

lemma sub_add_neg_sub_mul_eq_zero (m n r : ℤ) :
    (W (m - n) + W (-(m - n))) * W (m + n) * W r ^ 2 = 0 := by
  have := congr($(ell m n r) + $(ell n m r))
  rw [add_comm n, ← right_distrib, ← left_distrib, mul_comm (W _)] at this
  rw [show (-(m - n) : ℤ) = n - m by ring]
  convert this using 1; ring

variable (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
include one two

/-- An elliptic sequence is an odd function, provided its first two terms are not zero divisors. -/
lemma neg (m : ℤ) : W (-m) = - W m := by
  rw [eq_neg_iff_add_eq_zero]
  obtain ⟨m, rfl|rfl⟩ := m.even_or_odd'
  · refine two.2 _ ((pow_mem one 2).2 _ ?_)
    have := sub_add_neg_sub_mul_eq_zero ell (1 - ↑m) (↑m + 1) 1
    rw [show ((1 : ℤ) - ↑m - (↑m + 1)) = -(2 * ↑m) by omega,
      show ((1 : ℤ) - ↑m + (↑m + 1)) = 2 by omega] at this
    simpa [neg_neg] using this
  · refine one.2 _ ((pow_mem one 2).2 _ ?_)
    have := sub_add_neg_sub_mul_eq_zero ell (-↑m) (↑m + 1) 1
    rw [show ((-↑m : ℤ) - (↑m + 1)) = -(2 * ↑m + 1) by omega,
      show ((-↑m : ℤ) + (↑m + 1)) = 1 by omega] at this
    simpa [neg_neg] using this

protected lemma rel₄ {a b c d : ℤ} (same : HaveSameParity₄ a b c d) : rel₄ W a b c d = 0 :=
  rel₄_of_oddRec_evenRec (ell.neg one two) (ell.zero 1 two) one two
    (fun _ _ ↦ ell.oddRec _) (fun _ _ ↦ ell.evenRec _) same

protected lemma net (p q r s : ℤ) : net W p q r s = 0 := by
  rw [net_eq_rel₄]
  refine ell.rel₄ one two ?_
  simp_rw [HaveSameParity₄, Int.negOnePow_add, Int.negOnePow_two_mul, one_mul, true_and]

lemma invar (s m n : ℤ) : invarNum W s m * invarDenom W s n = invarNum W s n * invarDenom W s m :=
  invar_of_net _ (ell.net one two) _ _ _

end IsEllSequence

section NormEDS
variable (b c d : R)
open EllSequence

lemma normEDS_def (n : ℤ) :
    normEDS b c d n = preNormEDS (b ^ 4) c d n * if Even n then b else 1 := rfl

/- superseded by `IsEllSequence.normEDS` which doesn't require `hb`. -/
private theorem IsEllSequence.normEDS_of_mem_nonZeroDivisors (hb : b ∈ R⁰) :
    IsEllSequence (normEDS b c d) := by
  refine IsEllSequence.of_oddRec_evenRec (normEDS_neg _ _ _) (normEDS_zero _ _ _)
    (by rw [normEDS_one]; exact one_mem _) (by rwa [normEDS_two]) ?_ ?_ <;>
    intro m hm <;> rw [GE.ge, ← sub_nonneg] at hm
  · lift m - 2 to ℕ using hm with k hk
    rw [← eq_sub_iff_add_eq.mp hk, OddRec, normEDS_one, one_pow, mul_one]
    convert normEDS_odd b c d (↑k + 2) using 2
  · lift m - 3 to ℕ using hm with k hk
    rw [← eq_sub_iff_add_eq.mp hk, EvenRec, normEDS_one, normEDS_two, one_pow, mul_one]
    convert normEDS_even b c d (↑k + 3) using 1
    ring

lemma invarNum_normEDS (n : ℤ) : letI W := normEDS b c d
    invarNum W 1 n = W (n + 2) * W (n - 1) ^ 2 + W (n + 1) ^ 2 * W (n - 2) + W n ^ 3 * b ^ 2 := by
  simp [invarNum]

lemma invarNum_normEDS_two : invarNum (normEDS b c d) 1 2 = (d + b ^ 4) * b := by
  simp [invarNum, right_distrib, ← pow_succ, ← pow_add]

lemma invarDenom_normEDS_two : invarDenom (normEDS b c d) 1 2 = c * b := by simp [invarDenom]

section Complement

variable (b c d : R) (m : ℤ)

/-- An auxiliary expression that appears in the definition of the numerator of
the reduced invariant and in the definition of the `ω` family of division polynomials. -/
def compl₂EDSAux : R :=
  preNormEDS (b ^ 4) c d (m - 2) * preNormEDS (b ^ 4) c d (m + 1) ^ 2 * if Even m then 1 else b

@[simp] lemma compl₂EDSAux_zero : compl₂EDSAux b c d 0 = -1 := by simp [compl₂EDSAux]
@[simp] lemma compl₂EDSAux_one : compl₂EDSAux b c d 1 = -b := by simp [compl₂EDSAux]
@[simp] lemma compl₂EDSAux_neg_one : compl₂EDSAux b c d (-1) = 0 := by simp [compl₂EDSAux]
@[simp] lemma compl₂EDSAux_two : compl₂EDSAux b c d 2 = 0 := by simp [compl₂EDSAux]
@[simp] lemma compl₂EDSAux_neg_two : compl₂EDSAux b c d (-2) = -d := by simp [compl₂EDSAux]

lemma compl₂EDSAux_mul_b :
    compl₂EDSAux b c d m * b = normEDS b c d (m - 2) * normEDS b c d (m + 1) ^ 2 := by
  simp_rw [compl₂EDSAux, normEDS, Int.even_add, Int.even_sub, Int.not_even_one, even_two,
    iff_false, iff_true]; split_ifs <;> ring

/-- The "complement" of W(m) in W(2m) for a normalised EDS W is the witness of W(m) ∣ W(2m). -/
def compl₂EDS : R :=
  letI p := preNormEDS (b ^ 4) c d
  (p (m - 1) ^ 2 * p (m + 2) - p (m - 2) * p (m + 1) ^ 2) * if Even m then 1 else b

lemma compl₂EDSAux_neg : compl₂EDSAux b c d (-m) = -compl₂EDS b c d m - compl₂EDSAux b c d m := by
  simp_rw [compl₂EDSAux, compl₂EDS, neg_sub_left, neg_add_eq_sub, ← neg_sub m,
    preNormEDS_neg, even_neg]; ring_nf

@[simp] lemma compl₂EDS_zero : compl₂EDS b c d 0 = 2 := by simp [compl₂EDS, one_add_one_eq_two]
@[simp] lemma compl₂EDS_one : compl₂EDS b c d 1 = b := by simp [compl₂EDS]
@[simp] lemma compl₂EDS_two : compl₂EDS b c d 2 = d := by simp [compl₂EDS]

@[simp] lemma compl₂EDS_neg : compl₂EDS b c d (-m) = compl₂EDS b c d m := by
  simp_rw [compl₂EDS, neg_sub_left, neg_add_eq_sub, ← neg_sub m, preNormEDS_neg, even_neg]; ring_nf

lemma normEDS_mul_compl₂EDS :
    normEDS b c d m * compl₂EDS b c d m = normEDS b c d (2 * m) := by
  induction m using Int.negInduction with
  | nat m =>
    obtain _|_|_|m := m
    iterate 3 simp [mul_comm]
    simp_rw [show m + 1 + 1 + 1 = m + 3 by rfl, normEDS, compl₂EDS,
      ite_eq_left (even_two_mul _), Nat.cast_add, preNormEDS_even]
    rw [mul_mul_mul_comm]; congr 1
    · push_cast; ring
    · split_ifs <;> simp only [one_mul, mul_one]
  | neg hm m => simp_rw [mul_neg, normEDS_neg, compl₂EDS_neg, neg_mul, hm]

lemma normEDS_dvd_two_mul : normEDS b c d m ∣ normEDS b c d (2 * m) :=
  ⟨_, (normEDS_mul_compl₂EDS b c d m).symm⟩

lemma compl₂EDS_mul_b : letI W := normEDS b c d
    compl₂EDS b c d m * b = W (m - 1) ^ 2 * W (m + 2) - W (m - 2) * W (m + 1) ^ 2 := by
  induction m using Int.negInduction with
  | nat m =>
    simp_rw [compl₂EDS, normEDS, Int.even_sub, Int.even_add,
      Int.not_even_one, even_two, iff_false, iff_true]
    split_ifs <;> ring
  | neg hm m =>
    simp_rw [← neg_add', neg_add_eq_sub, ← neg_sub (m : ℤ), normEDS_neg, compl₂EDS_neg]
    convert hm m using 1; ring

lemma normEDS_six_eq_mul : normEDS b c d 6 = (normEDS b c d 5 - d ^ 2) * b * c := by
  rw [show (6 : ℤ) = 2 * 3 by rfl, ← normEDS_mul_compl₂EDS, compl₂EDS, ite_eq_right (by decide)]
  simp_rw [Int.reduceAdd, Int.reduceSub, normEDS_three, normEDS]
  rw [preNormEDS_one, preNormEDS_two, preNormEDS_four, ite_eq_right (by decide)]
  ring

namespace EllSequence

variable (W₁ compl₂ : ℤ → R) (m : ℤ)

/-- Given two sequences representing `W(m)/W(1)` and `W(2m)/W(m)` respectively,
we construct the sequence representing `W(n*m)/W(m)` in a division-free way. -/
def compl' : ℕ → R
  | 0 => 0
  | 1 => 1
  | (n + 2) => letI k := n / 2 + 1
    have : k < n + 2 := by omega
    if hn : Even n
      then compl₂ (k * m) * compl' k
      else
        have : k + 1 < n + 2 := by
          have := (Nat.not_even_iff_odd.mp hn).pos; omega
        W₁ ((k + 1) * m + 1) * W₁ ((k + 1) * m - 1) * compl' k ^ 2
      - W₁ (k * m + 1) * W₁ (k * m - 1) * compl' (k + 1) ^ 2

/-- `W(n*m)/W(m)` with `n : ℤ`. -/
def compl (n : ℤ) : R := n.sign * compl' W₁ compl₂ m n.natAbs

lemma compl_ofNat (n : ℕ) : compl W₁ compl₂ m n = compl' W₁ compl₂ m n := by
  obtain _|n := n; · simp [compl, compl']
  simp only [compl, Int.sign_natCast_of_ne_zero (Nat.succ_ne_zero n),
    Int.cast_one, one_mul, Int.natAbs_natCast]

lemma compl_neg (n : ℤ) : compl W₁ compl₂ m (-n) = -compl W₁ compl₂ m n := by
  simp [compl, Int.sign_neg, Int.natAbs_neg, neg_mul]

/-- `W(n*m)/W(m)` for `W` a normalised EDS. -/
def auxComplEDS := compl (normEDS b c d) (compl₂EDS b c d) m

end EllSequence

end Complement

section Map

variable {b c d}

lemma map_compl₂EDS (n : ℤ) : f (compl₂EDS b c d n) = compl₂EDS (f b) (f c) (f d) n := by
  simp only [compl₂EDS, map_sub, map_mul, map_pow, map_preNormEDS, apply_ite f, map_one]

lemma EllSequence.map_compl' (W₁ compl₂ : ℤ → R) (m : ℤ) (n : ℕ) :
    f (compl' W₁ compl₂ m n) = compl' (f ∘ W₁) (f ∘ compl₂) m n := by
  refine n.strong_induction_on fun n ih ↦ ?_
  obtain _|_|n := n
  iterate 2 simp [compl']
  rw [compl']; conv_rhs => rw [compl']
  split_ifs with hn
  · rw [map_mul, ih _ (by omega)]; rfl
  simp_rw [map_sub, map_mul, map_pow]
  rw [ih _ (by omega), ih]; · rfl
  · have := (Nat.not_even_iff_odd.mp hn).pos; omega

lemma EllSequence.map_compl (W₁ compl₂ : ℤ → R) (m n : ℤ) :
    f (compl W₁ compl₂ m n) = compl (f ∘ W₁) (f ∘ compl₂) m n := by
  simp [compl, map_compl']

lemma map_auxComplEDS (m n : ℤ) :
    f (auxComplEDS b c d m n) = auxComplEDS (f b) (f c) (f d) m n := by
  simp only [auxComplEDS, EllSequence.map_compl]
  congr 1
  · ext x; simp only [Function.comp, map_normEDS]
  · ext x; simp only [Function.comp, map_compl₂EDS]

lemma map_addMulSub (m n : ℤ) : f (addMulSub W m n) = addMulSub (f ∘ W) m n := by
  simp_rw [addMulSub, map_mul, Function.comp]

lemma map_rel₄ (p q r s : ℤ) : f (rel₄ W p q r s) = rel₄ (f ∘ W) p q r s := by
  simp_rw [rel₄, map_add, map_sub, map_mul, map_addMulSub]

lemma map_net (p q r s : ℤ) : f (net W p q r s) = net (f ∘ W) p q r s := by
  simp_rw [net_eq_rel₄, map_rel₄]

lemma map_invarNum (s m : ℤ) : f (invarNum W s m) = invarNum (f ∘ W) s m := by
  simp only [invarNum, map_add, map_mul, map_pow, Function.comp]

lemma map_invarDenom (s m : ℤ) : f (invarDenom W s m) = invarDenom (f ∘ W) s m := by
  simp_rw [invarDenom, map_mul, Function.comp]

/-- A type of three elements corresponding to the three parameters of a normalised EDS. -/
inductive Param : Type | B : Param | C : Param | D : Param

open Param MvPolynomial
/-- The universal normalised EDS, from which every normalised EDS can be obtained by
composing with a ring homomorphism, which allows us to reduce equalities between
expressions involving terms of a normalised EDS to the universal case.
It takes values in a domain, and all nonzero terms are nonzero and therefore
are not zero divisors, a condition required to apply certain lemmas. -/
noncomputable def universalNormEDS : ℤ → MvPolynomial Param ℤ := normEDS (X B) (X C) (X D)

lemma normEDS_eq_aeval : normEDS b c d = (aeval (Param.rec b c d) <| universalNormEDS ·) := by
  simp_rw [universalNormEDS, map_normEDS, aeval_X]

lemma compl₂EDS_eq_aeval :
    compl₂EDS b c d =
      (aeval (Param.rec b c d) <| compl₂EDS (X (R := ℤ) B) (X C) (X D) ·) := by
  simp_rw [map_compl₂EDS, aeval_X]

lemma auxComplEDS_eq_aeval :
    auxComplEDS b c d =
      (aeval (Param.rec b c d) <| auxComplEDS (X (R := ℤ) B) (X C) (X D) · ·) := by
  simp_rw [map_auxComplEDS, aeval_X]

end Map

section

variable {b c d} {U : ℤ → R} (ellW : IsEllSequence W) (ellU : IsEllSequence U)
include ellW ellU
open MvPolynomial

omit ellW ellU in
/-- A normalised EDS is in fact an elliptic sequenc. -/
protected lemma IsEllSequence.normEDS : IsEllSequence (normEDS b c d) := by
  rw [normEDS_eq_aeval]
  exact map _ (normEDS_of_mem_nonZeroDivisors _ _ _ (mem_nonZeroDivisors_of_ne_zero <| X_ne_zero _))

/-- Two elliptic sequences are equal if their first four terms are equal,
provided the first two terms are not zero divisors. -/
protected lemma IsEllSequence.ext (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
    (h1 : W 1 = U 1) (h2 : W 2 = U 2) (h3 : W 3 = U 3) (h4 : W 4 = U 4) : W = U :=
  funext fun n ↦ by
    induction n using Int.negInduction with
    | nat n =>
      refine normEDSRec ?_ h1 h2 h3 h4 (fun m h₁ h₂ h₃ h₄ h₅ ↦ ?_) (fun m h₁ h₂ h₃ h₄ ↦ ?_) n
      · rw [Nat.cast_zero, ellW.zero 1 two, ellU.zero 1 (h2 ▸ two)]
      · erw [← mul_cancel_right_mem_nonZeroDivisors (mul_mem two <| pow_mem one 2), ← mul_assoc,
          ← mul_assoc, Nat.cast_mul, Nat.cast_add, ellW.evenRec, h1, h2, ellU.evenRec]
        convert congr($h₃ * ($h₂ ^ 2 * $h₅ - $h₁ * $h₄ ^ 2)) <;> abel
      · rw [← mul_cancel_right_mem_nonZeroDivisors (pow_mem one 3)]
        erw [Nat.cast_add, Nat.cast_mul, Nat.cast_add, ellW.oddRec, h1, ellU.oddRec]
        convert congr($h₄ * $h₂ ^ 3 - $h₁ * $h₃ ^ 3) <;> abel
    | neg hn n =>
      rw [ellW.neg one two, ellU.neg (h1 ▸ one) (h2 ▸ two), hn]

omit ellW ellU in
lemma normEDS_two_three_two : normEDS (2 : ℤ) 3 2 = id := by
  apply IsEllSequence.ext IsEllSequence.normEDS isEllSequence_id <;>
    simp only [normEDS_one, normEDS_two, normEDS_three, normEDS_four]
  exacts [mem_nonZeroDivisors_of_ne_zero one_ne_zero,
    mem_nonZeroDivisors_of_ne_zero two_ne_zero, rfl, rfl, rfl, rfl]

omit ellW ellU in
lemma compl₂EDS_two_three_two (n : ℤ) : compl₂EDS (2 : ℤ) 3 2 n = 2 := by
  obtain rfl | hn := eq_or_ne n 0
  · exact compl₂EDS_zero ..
  · have := normEDS_mul_compl₂EDS (2 : ℤ) 3 2 n
    rw [normEDS_two_three_two] at this
    simp only [id] at this
    exact mul_right_cancel₀ hn (by linarith)

omit ellW ellU in
lemma universalNormEDS_ne_zero {n : ℤ} (hn : n ≠ 0) : universalNormEDS n ≠ 0 :=
  fun h ↦ hn <| by
    apply_fun aeval (Param.rec (2 : ℤ) 3 2) at h
    simp only [universalNormEDS, map_normEDS, aeval_X, normEDS_two_three_two, map_zero] at h
    exact_mod_cast h

omit ellW ellU in
lemma universalNormEDS_mem_nonZeroDivisors {n : ℤ} (hn : n ≠ 0) :
    universalNormEDS n ∈ (MvPolynomial Param ℤ)⁰ :=
  mem_nonZeroDivisors_of_ne_zero (universalNormEDS_ne_zero hn)

section Divisibility

variable (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
  (dvd₁₂ : W 1 ∣ W 2) (dvd₁₃ : W 1 ∣ W 3) (dvd₂₄ : W 2 ∣ W 4)
include one two dvd₁₂ dvd₁₃ dvd₂₄

omit ellU one in
/-- An elliptic sequence whose second term is not a zero divisor and which divides its second,
third and fourth terms appropriately is a constant multiple of a normalised EDS.
The first term is automatically not a zero divisor: it divides `W 2 ∈ R⁰`. -/
theorem IsEllSequence.eq_normEDS_of_dvd : ∃ b c d, W = (W 1 * normEDS b c d ·) :=
  have ⟨b, h₁₂⟩ := dvd₁₂; have ⟨c, h₁₃⟩ := dvd₁₃; have ⟨d, h₂₄⟩ := dvd₂₄
  have one : W 1 ∈ R⁰ := (mul_mem_nonZeroDivisors.mp (h₁₂ ▸ two)).1
  ⟨b, c, d, @IsEllSequence.ext _ _ _ _ ellW (IsEllSequence.smul IsEllSequence.normEDS _)
    one two (by simp) (by simp [h₁₂]) (by simp [h₁₃]) (by rw [h₂₄, h₁₂, normEDS_four]; ring)⟩

omit ellW ellU one dvd₁₂ dvd₁₃ dvd₂₄ in
/-- An EDS whose second term is not a zero divisor
is a constant multiple of a normalised EDS. -/
theorem IsEllDivSequence.eq_normEDS (h : IsEllDivSequence W) :
    ∃ b c d, W = (W 1 * normEDS b c d ·) :=
  h.1.eq_normEDS_of_dvd two (h.2 _ _ ⟨2, by ring⟩) (h.2 _ _ ⟨3, by ring⟩) (h.2 _ _ ⟨2, by ring⟩)

section Complement

variable (W₁ compl₂ : ℤ → R)
  (h₁ : ∀ m, W 1 * W₁ m = W m) (h₂ : ∀ m, W m * compl₂ m = W (2 * m)) (m n : ℤ)

include h₁ h₂

omit ellU dvd₁₂ dvd₁₃ dvd₂₄ in
/-- If `W` is an elliptic sequence whose first two terms are not zero divisors,
the sequence constructed above indeed gives `W(n*m)` when multiplied by `W(m)`.
The condition `mem` is actually redundant because `W` is a multiple of a normalised EDS
by the other assumptions, so we can conclude using `normEDS_mul_compl` below. -/
lemma IsEllSequence.mul_compl_eq_apply_mul_of_mem_nonZeroDivisors (mem : W m ∈ R⁰) :
    W m * compl W₁ compl₂ m n = W (n * m) := by
  induction n using Int.negInduction with
  | nat n =>
    refine n.strong_induction_on fun n ih ↦ ?_
    obtain _ | n := n; · simp [EllSequence.compl, ellW.zero 1 two]
    obtain _ | n := n; · simp [EllSequence.compl, compl']
    rw [EllSequence.compl, Int.sign_eq_one_of_pos (by omega),
      Int.natAbs_natCast, compl', Int.cast_one, one_mul]
    obtain ⟨k, rfl|rfl⟩ := n.even_or_odd'
    · simp only [dite_eq_left (even_two_mul _), k.mul_div_cancel_left zero_lt_two]
      rw [mul_comm (compl₂ _),
        ← mul_assoc, ← compl_ofNat, ih _ (by omega), h₂, ← mul_assoc, add_assoc, ← two_mul,
        ← left_distrib, Nat.cast_mul]; rfl
    simp_rw [dite_eq_right (Nat.not_even_two_mul_add_one _), show (2 * k + 1) / 2 = k by omega]
    rw [← mul_cancel_right_mem_nonZeroDivisors (mul_mem mem <| pow_mem one 2)]
    have := (ellW ((k + 1 + 1) * m) ((k + 1) * m) 1).symm
    simp_rw [← right_distrib, ← mul_sub_right_distrib, add_sub_cancel_left,
      ← h₁ (_ + 1), ← h₁ (_ - 1), ← Nat.cast_one (R := ℤ), ← Nat.cast_add] at this
    rw [← ih _ (by omega), ← ih _ (by omega)] at this
    simp_rw [compl_ofNat, Nat.cast_add] at this ⊢
    convert this using 1
    · push_cast; ring
    push_cast; ring_nf
  | neg hn n => rw [neg_mul, ellW.neg one two, compl_neg, mul_neg, hn n]

omit ellW ellU one two dvd₁₂ dvd₁₃ dvd₂₄ h₁ h₂ in
private lemma normEDS_mul_auxComplEDS_of_mem (hb : b ∈ R⁰) {m : ℤ}
    (hm : normEDS b c d m ∈ R⁰) (n : ℤ) :
    normEDS b c d m * auxComplEDS b c d m n = normEDS b c d (n * m) := by
  change normEDS b c d m * compl (normEDS b c d) (compl₂EDS b c d) m n = normEDS b c d (n * m)
  exact IsEllSequence.mul_compl_eq_apply_mul_of_mem_nonZeroDivisors
    IsEllSequence.normEDS
    (by rw [normEDS_one]; exact one_mem _)
    (by rw [normEDS_two]; exact hb)
    (normEDS b c d) (compl₂EDS b c d)
    (fun m ↦ by rw [normEDS_one, one_mul])
    (normEDS_mul_compl₂EDS b c d)
    m n hm

omit ellW ellU one two dvd₁₂ dvd₁₃ dvd₂₄ h₁ h₂ in
open Param in
lemma normEDS_mul_auxComplEDS (m n : ℤ) :
    normEDS b c d m * auxComplEDS b c d m n = normEDS b c d (n * m) := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [normEDS_zero, mul_comm n 0]
  · have := congr(aeval (Param.rec b c d) $(normEDS_mul_auxComplEDS_of_mem
      (b := X (R := ℤ) B) (c := X C) (d := X D)
      (mem_nonZeroDivisors_of_ne_zero <| X_ne_zero _)
      (universalNormEDS_mem_nonZeroDivisors hm) n))
    simpa only [map_mul, map_normEDS, map_auxComplEDS, aeval_X] using this

omit ellW ellU one two dvd₁₂ dvd₁₃ dvd₂₄ h₁ h₂ in
lemma normEDS_mul_auxComplEDS_div {m : ℤ} (n : ℤ) (dvd : m ∣ n) :
    normEDS b c d m * auxComplEDS b c d m (n / m) = normEDS b c d n := by
  rcases eq_or_ne m 0 with rfl | hm
  · obtain ⟨n, rfl⟩ := dvd; simp
  · obtain ⟨n, rfl⟩ := dvd
    rw [Int.mul_ediv_cancel_left _ hm, normEDS_mul_auxComplEDS, mul_comm]

namespace EllSequence

omit ellW ellU one two dvd₁₂ dvd₁₃ dvd₂₄ h₁ h₂

variable (b c d)

/-- The numerator of the reduced invariant expression `(W(m-1)²W(m+2)+W(m-2)W(m+1)²+W₂²W(m)³)/W₂`
for a normalised EDS W, obtained by cancelling `W₃W₂ = b*c` from `invarNum`. -/
def redInvarNum : R :=
  compl₂EDS b c d m + normEDS b c d m ^ 3 * b + 2 * compl₂EDSAux b c d m

lemma compl₂EDS_eq_redInvarNum_sub :
    compl₂EDS b c d m =
      redInvarNum b c d m - normEDS b c d m ^ 3 * b - 2 * compl₂EDSAux b c d m := by
  rw [redInvarNum]; ring

lemma invarNum_eq_redInvarNum_mul : invarNum (normEDS b c d) 1 m = redInvarNum b c d m * b := by
  simp_rw [redInvarNum, right_distrib, compl₂EDS_mul_b, mul_assoc 2 _ b,
    compl₂EDSAux_mul_b, invarNum_normEDS]; ring

/-- The expression `W(m+1)W(m)W(m-1)/W₃W₂` for a normalised EDS. -/
def redInvarDenom : R :=
  letI C := auxComplEDS b c d
  letI W := normEDS b c d
  letI r₆ := normEDS b c d 5 - d ^ 2 -- W₆/W₃W₂
  if m % 6 = 0 then r₆ * C 6 (m / 6) * W (m + 1) * W (m - 1) else
  if m % 6 = 1 then r₆ * C 6 ((m - 1) / 6) * W (m + 1) * W m else
  if m % 6 = 5 then r₆ * C 6 ((m + 1) / 6) * W m * W (m - 1) else
  if m % 6 = 2 then C 3 ((m + 1) / 3) * C 2 (m / 2) * W (m - 1) else
  if m % 6 = 4 then C 3 ((m - 1) / 3) * C 2 (m / 2) * W (m + 1) else
  if m % 6 = 3 then C 3 (m / 3) * C 2 ((m - 1) / 2) * W (m + 1) else 0

lemma invarDenom_eq_redInvarDenom_mul :
    invarDenom (normEDS b c d) 1 m = redInvarDenom b c d m * b * c := by
  have h6 : (6 : ℤ) ≠ 0 := by decide
  have h3 : (3 : ℤ) ≠ 0 := by decide
  have hd k m dvd eq :=
    (@Int.dvd_iff_emod_eq_zero k m).mpr ((@Int.emod_emod_of_dvd m k 6 dvd).symm.trans eq)
  have hd2 {m} := hd 2 m ⟨3, rfl⟩
  have hd3 {m} := hd 3 m ⟨2, rfl⟩
  rw [invarDenom, redInvarDenom]; split_ifs with h h h h h h -- slow
  · rw [← normEDS_mul_auxComplEDS_div _ (Int.dvd_of_emod_eq_zero h), normEDS_six_eq_mul]; ring
  · rw [← normEDS_mul_auxComplEDS_div _ (Int.dvd_self_sub_of_emod_eq h), normEDS_six_eq_mul]; ring
  · rw [show m + 1 = m + 6 - 5 by abel, ← normEDS_mul_auxComplEDS_div _
      (Int.dvd_self_sub_of_emod_eq (Int.emod_eq_add_self_emod.symm.trans h)),
      normEDS_six_eq_mul]; ring
  on_goal 1 => rw [← normEDS_mul_auxComplEDS_div _ (hd3 <| by simp [h, Int.add_emod]),
    ← normEDS_mul_auxComplEDS_div m (hd2 <| by simp [h])]
  on_goal 2 => rw [← normEDS_mul_auxComplEDS_div (m - 1) (hd3 <| by simp [h, Int.sub_emod]),
    ← normEDS_mul_auxComplEDS_div m (hd2 <| by simp [h])]
  on_goal 3 => rw [← normEDS_mul_auxComplEDS_div m (hd3 <| by simp [h]),
    ← normEDS_mul_auxComplEDS_div (m - 1) (hd2 <| by simp [h, Int.sub_emod])]
  on_goal 4 =>
    have h0 := Int.emod_nonneg m h6
    have lt := Int.emod_lt_of_pos m (show 0 < 6 by decide)
    interval_cases m % 6 <;> contradiction
  all_goals rw [normEDS_three, normEDS_two]; ring

@[simp] lemma redInvarDenom_zero : redInvarDenom b c d 0 = 0 := by
  simp [redInvarDenom, auxComplEDS, compl', compl]

@[simp] lemma redInvarDenom_one : redInvarDenom b c d 1 = 0 := by
  simp [redInvarDenom, auxComplEDS, compl', compl]

@[simp] lemma redInvarDenom_two : redInvarDenom b c d 2 = 1 := by
  simp [redInvarDenom, auxComplEDS, compl', compl]

lemma map_compl₂EDSAux : f (compl₂EDSAux b c d m) = compl₂EDSAux (f b) (f c) (f d) m := by
  simp [compl₂EDSAux, apply_ite f, map_preNormEDS]

lemma map_redInvarNum : f (redInvarNum b c d m) = redInvarNum (f b) (f c) (f d) m := by
  simp only [redInvarNum, map_add, map_mul, map_pow, map_compl₂EDS, map_normEDS,
    map_compl₂EDSAux, map_ofNat]

lemma map_redInvarDenom : f (redInvarDenom b c d m) = redInvarDenom (f b) (f c) (f d) m := by
  simp [redInvarDenom, apply_ite f, map_normEDS, map_auxComplEDS]

end EllSequence

end Complement

omit ellW ellU one two dvd₁₂ dvd₁₃ dvd₂₄ in
/-- A normalised EDS is in fact a divisibility sequence. -/
protected theorem IsDivSequence.normEDS : IsDivSequence (normEDS b c d) := by
  intro m n ⟨k, hk⟩
  rw [hk, mul_comm m k]
  exact ⟨_, (normEDS_mul_auxComplEDS m k).symm⟩

omit ellW ellU one two dvd₁₂ dvd₁₃ dvd₂₄ in
/-- A normalised EDS is in fact an EDS. -/
protected theorem IsEllDivSequence.normEDS : IsEllDivSequence (normEDS b c d) :=
  ⟨IsEllSequence.normEDS, IsDivSequence.normEDS⟩

omit ellU one in
/-- An elliptic sequence is a divisibility sequence if it satisfies three base cases
of the divisibility condition, provided its second term is not a zero divisor. -/
lemma IsEllSequence.isDivSequence_of_dvd : IsDivSequence W := by
  obtain ⟨b, c, d, h⟩ := ellW.eq_normEDS_of_dvd two dvd₁₂ dvd₁₃ dvd₂₄
  intro m n hmn
  rw [congr_fun h m, congr_fun h n]
  exact mul_dvd_mul_left (W 1) (IsDivSequence.normEDS m n hmn)

omit ellU one in
lemma IsEllSequence.isEllDivSequence_of_dvd : IsEllDivSequence W :=
  ⟨ellW, ellW.isDivSequence_of_dvd two dvd₁₂ dvd₁₃ dvd₂₄⟩

end Divisibility

section

omit ellW ellU in
lemma net_normEDS (p q r s : ℤ) : net (normEDS b c d) p q r s = 0 := by
  rw [normEDS_eq_aeval, show (aeval (Param.rec b c d) <| universalNormEDS ·) =
    (⇑(aeval (Param.rec b c d))) ∘ universalNormEDS from rfl, ← map_net,
    universalNormEDS, IsEllSequence.normEDS.net, map_zero] <;>
  apply mem_nonZeroDivisors_of_ne_zero <;> simp only [normEDS_one, normEDS_two]
  exacts [one_ne_zero, MvPolynomial.X_ne_zero _]

omit ellW ellU in
lemma rel₄_normEDS (p q r s : ℤ) (same : HaveSameParity₄ p q r s) :
    rel₄ (normEDS b c d) p q r s = 0 := by
  rw [same.rel₄_eq_net, net_normEDS]

omit ellW ellU in
lemma invar_normEDS (s m n : ℤ) :
    invarNum (normEDS b c d) s m * invarDenom (normEDS b c d) s n =
      invarNum (normEDS b c d) s n * invarDenom (normEDS b c d) s m :=
  invar_of_net _ net_normEDS _ _ _

omit ellW ellU in
private lemma invar₂_normEDS_of_mem_nonZeroDivisors (hb : b ∈ R⁰) (m : ℤ) :
    invarNum (normEDS b c d) 1 m * c = invarDenom (normEDS b c d) 1 m * (d + b ^ 4) := by
  rw [← mul_cancel_right_mem_nonZeroDivisors hb, mul_assoc, mul_assoc, mul_comm (invarDenom _ _ _)]
  convert invar_normEDS 1 m (2 : ℤ) <;> simp only [invarNum_normEDS_two, invarDenom_normEDS_two]

omit ellW ellU in
open MvPolynomial Param in
lemma invar₂_normEDS {m : ℤ} :
    invarNum (normEDS b c d) 1 m * c = invarDenom (normEDS b c d) 1 m * (d + b ^ 4) := by
  have := congr(aeval (Param.rec b c d) $(invar₂_normEDS_of_mem_nonZeroDivisors
    (c := X Param.C) (d := X D) (mem_nonZeroDivisors_of_ne_zero <| X_ne_zero (R := ℤ) B) m))
  rw [← universalNormEDS] at this
  simp only [map_mul, map_invarNum, map_invarDenom, map_add, map_pow, aeval_X] at this
  rwa [show (⇑(aeval fun t ↦ Param.rec b c d t) ∘ universalNormEDS) =
    normEDS b c d from funext fun n ↦ by simp [universalNormEDS, map_normEDS, aeval_X]] at this

omit ellW ellU in
private lemma redInvar_normEDS_of_mem_nonZeroDivisors (hb : b ∈ R⁰) (hc : c ∈ R⁰) (m : ℤ) :
    redInvarNum b c d m = redInvarDenom b c d m * (d + b ^ 4) := by
  rw [← mul_cancel_right_mem_nonZeroDivisors hb, ← mul_cancel_right_mem_nonZeroDivisors hc,
    ← invarNum_eq_redInvarNum_mul, invar₂_normEDS, invarDenom_eq_redInvarDenom_mul]
  ring

omit ellW ellU in
open MvPolynomial Param in
lemma redInvar_normEDS (m : ℤ) :
    redInvarNum b c d m = redInvarDenom b c d m * (d + b ^ 4) := by
  have := congr(aeval (Param.rec b c d) $(redInvar_normEDS_of_mem_nonZeroDivisors
    (b := X (R := ℤ) B) (c := X Param.C) (d := X D) ?_ ?_ m))
  · simpa only [map_redInvarNum, map_mul, map_add, map_pow, map_redInvarDenom, aeval_X] using this
  all_goals exact mem_nonZeroDivisors_of_ne_zero (X_ne_zero _)

end

end

end NormEDS


end FLT.NTorsionAux

end

/-!
Ported from mathlib PR #41197, revision
`f46c499f84960839eac3fdbc517a930f02b3b252`
(https://github.com/leanprover-community/mathlib4/pull/41197).

# Additions to Affine.Point and the universal elliptic curve

This file provides lemmas missing from the released mathlib that are needed for the
division polynomial / ZSMul development:
- `algebraMap_poly_injective` and `algebraMap_injective'` (injectivity of `algebraMap` into
  the coordinate ring)
- `some_eq_some_iff` (point equality for nonsingular affine points)

It also defines the universal Weierstrass curve (`Universal.curve`) over the
polynomial ring `ℤ[A₁,A₂,A₃,A₄,A₆]`, and the universal pointed elliptic curve
(`Universal.pointedCurve`) over the field of fractions (`Universal.Field`) of
`Universal.Ring = Universal.Poly/⟨P⟩ = ℤ[A₁,A₂,A₃,A₄,A₆,X,Y]/⟨P⟩` (where `P` is the Weierstrass
polynomial) with distinguished point `(X,Y)`.

Given a Weierstrass curve `W` over a commutative ring `R`, we define the specialization
homomorphism `W.specialize : ℤ[A₁,A₂,A₃,A₄,A₆] →+* R`. If `(x,y)` is a point on the affine plane,
we define `W.polyEval x y : Universal.Poly →+* R`, which factors through
`W.ringEval x y : Universal.Ring →+* R` if `(x,y)` is on `W`.

We also introduce the cusp curve `Y² = X³`, on which lies the rational point `(1,1)`, with
the nice property that `ψₙ(1,1) = n`, making it easy to prove nonvanishing of the universal `ψₙ`
when `n ≠ 0` by specializing to the cusp curve, which shows that `(X,Y)` is a point of infinite
order on the universal pointed elliptic curve.
-/

@[expose] public section
noncomputable section

/-! ## Point.lean additions -/

namespace WeierstrassCurve.Affine.CoordinateRing

open Polynomial

variable {R : Type*} [CommRing R] {W' : WeierstrassCurve.Affine R}

set_option backward.isDefEq.respectTransparency false in
lemma algebraMap_poly_injective : Function.Injective (algebraMap R[X] W'.CoordinateRing) :=
  (injective_iff_map_eq_zero _).mpr fun p hp ↦ And.left <|
    smul_basis_eq_zero (W' := W') (q := 0) <| by
      rwa [Algebra.smul_def, mul_one, zero_smul, add_zero]

lemma algebraMap_injective' : Function.Injective (algebraMap R W'.CoordinateRing) :=
  (CoordinateRing.algebraMap_poly_injective (W' := W')).comp C_injective

end WeierstrassCurve.Affine.CoordinateRing

namespace WeierstrassCurve.Affine.Point

variable {R : Type*} [CommRing R] {W' : WeierstrassCurve.Affine R}

lemma some_eq_some_iff {x₁ x₂ y₁ y₂ : R} (h₁ : W'.Nonsingular x₁ y₁)
    (h₂ : W'.Nonsingular x₂ y₂) : some x₁ y₁ h₁ = some x₂ y₂ h₂ ↔ x₁ = x₂ ∧ y₁ = y₂ :=
  ⟨by rintro (_ | _); trivial, by rintro ⟨rfl, rfl⟩; rfl⟩

end WeierstrassCurve.Affine.Point

/-! ## The universal elliptic curve -/

open scoped Polynomial.Bivariate

namespace WeierstrassCurve

/-- A type whose elements represent the five coefficients `a₁`, `a₂`, `a₃`, `a₄` and `a₆`
of the Weierstrass polynomial. -/
inductive Coeff : Type | A₁ : Coeff | A₂ : Coeff | A₃ : Coeff | A₄ : Coeff | A₆ : Coeff

namespace Universal

open scoped Polynomial Polynomial.Bivariate
open Coeff

open MvPolynomial (X) in
/-- The universal Weierstrass curve over the polynomial ring in five variables
(the **universal polynomial ring** for Weierstrass curves),
corresponding to the five coefficients of the Weierstrass polynomial. -/
def curve : Affine (MvPolynomial Coeff ℤ) :=
  { a₁ := X A₁, a₂ := X A₂, a₃ := X A₃, a₄ := X A₄, a₆ := X A₆ }

lemma Δ_curve_ne_zero : curve.Δ ≠ 0 := fun h ↦ by
  simp_rw [Δ, b₂, b₄, b₆, b₈, curve] at h
  apply_fun MvPolynomial.eval (Coeff.rec 0 0 0 0 1) at h
  simp at h

/-- The polynomial ring over ℤ in the variables `A₁`, `A₂`, `A₃`, `A₄`, `A₆`, `X` and `Y`,
which is the polynomial ring in two variables over the universal polynomial ring. -/
abbrev Poly : Type := (MvPolynomial Coeff ℤ)[X][Y]
/-- The universal ring for **pointed** Weierstrass curves. -/
protected abbrev Ring : Type := curve.CoordinateRing
/-- The universal field for pointed Weierstrass curves is
the field of fractions of the universal ring. -/
protected abbrev Field : Type := FractionRing Universal.Ring

instance : CommRing Poly := Polynomial.commRing /- why is this not automatic ... -/

lemma Poly.two_ne_zero : (2 : Poly) ≠ 0 :=
  Polynomial.C_ne_zero.mpr <| Polynomial.C_ne_zero.mpr fun h ↦ two_ne_zero' (α := ℤ) <|
    MvPolynomial.C_injective _ _ <| by rwa [← MvPolynomial.C_0] at h

/-- The obvious ring homomorphism from the polynomial ring in 7 variables to the universal field. -/
def polyToField : Poly →+* Universal.Field := (algebraMap Universal.Ring _).comp <| AdjoinRoot.mk _

lemma polyToField_apply (p : Poly) :
    polyToField p = algebraMap Universal.Ring _ (AdjoinRoot.mk _ p) := rfl

lemma algebraMap_field_eq_comp :
    algebraMap (MvPolynomial Coeff ℤ) Universal.Field = polyToField.comp (algebraMap _ _) := rfl

lemma algebraMap_ring_eq_comp :
    algebraMap (MvPolynomial Coeff ℤ) Universal.Ring = (AdjoinRoot.mk _).comp (algebraMap _ _) :=
  rfl

@[simp] lemma polyToField_polynomial : polyToField curve.polynomial = 0 := by
  rw [polyToField_apply, AdjoinRoot.mk_self, map_zero]

lemma algebraMap_field_injective :
    Function.Injective (algebraMap (MvPolynomial Coeff ℤ) Universal.Field) :=
  (IsFractionRing.injective Universal.Ring Universal.Field).comp
    (Affine.CoordinateRing.algebraMap_injective' (W' := curve))

/-- The universal pointed Weierstrass curve is an elliptic curve
when base-changed to the universal field. -/
abbrev pointedCurve : WeierstrassCurve Universal.Field := baseChange curve Universal.Field

instance : pointedCurve.IsElliptic where
  isUnit := by
    rw [show pointedCurve.Δ = _ from map_Δ curve (algebraMap _ Universal.Field)]
    exact ((map_ne_zero_iff _ algebraMap_field_injective).mpr Δ_curve_ne_zero).isUnit

open Polynomial in
lemma equation_point : pointedCurve.toAffine.Equation (polyToField (C X)) (polyToField Y) := by
  change evalEval (polyToField (C X)) (polyToField Y)
    ((curve.map (algebraMap _ Universal.Field)).toAffine.polynomial) = 0
  have h : (evalEvalRingHom (polyToField (C X)) (polyToField Y)).comp
      (mapRingHom <| mapRingHom (algebraMap _ Universal.Field)) = polyToField := by
    ext <;> simp [polyToField, algebraMap_field_eq_comp]
  have : ∀ p, evalEval (polyToField (C X)) (polyToField Y)
      (p.map (mapRingHom (algebraMap _ Universal.Field))) = polyToField p :=
    fun p ↦ congr($h p)
  rw [Affine.map_polynomial, this, polyToField_polynomial]

open Polynomial Affine in
/-- The distinguished point on the universal pointed Weierstrass curve. -/
def Affine.point : (curve.baseChange Universal.Field).toAffine.Point :=
  .mk equation_point

/-- The distinguished point on the universal curve in Jacobian coordinates. -/
def Jacobian.point : Jacobian.Point (curve.baseChange Universal.Field) :=
  Jacobian.Point.fromAffine Affine.point

open Polynomial (CC)

@[simp] lemma pointedCurve_a₁ : pointedCurve.a₁ = polyToField (CC curve.a₁) := rfl
@[simp] lemma pointedCurve_a₂ : pointedCurve.a₂ = polyToField (CC curve.a₂) := rfl
@[simp] lemma pointedCurve_a₃ : pointedCurve.a₃ = polyToField (CC curve.a₃) := rfl
@[simp] lemma pointedCurve_a₄ : pointedCurve.a₄ = polyToField (CC curve.a₄) := rfl
@[simp] lemma pointedCurve_a₆ : pointedCurve.a₆ = polyToField (CC curve.a₆) := rfl

/-- The base change of the universal curve from `ℤ[A₁,⋯,A₆]` to `ℤ[A₁,⋯,A₆,X,Y]`. -/
abbrev curvePoly : WeierstrassCurve Poly := curve.baseChange Poly
/-- The base change of the universal curve from `ℤ[A₁,⋯,A₆]` to `ℤ[A₁,⋯,A₆,X,Y]/⟨P⟩`
(the universal ring), where `P` is the Weierstrass polynomial. -/
abbrev curveRing : WeierstrassCurve Universal.Ring := curve.baseChange Universal.Ring
/-- The base change of the universal curve from `ℤ[A₁,⋯,A₆]` to `Frac(ℤ[A₁,⋯,A₆,X,Y]/⟨P⟩)`
(the universal field), where `P` is the Weierstrass polynomial. -/
abbrev curveField : WeierstrassCurve Universal.Field := curve.baseChange Universal.Field

lemma curveField_eq : curveField = pointedCurve := rfl

end Universal

/-- The cusp curve $Y^2 = X^3$ over a commutative ring `R`. -/
def cusp (R : Type*) [CommRing R] : Affine R := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := 0 }

lemma cusp_equation_one_one : (cusp ℤ).Equation 1 1 := by
  simp [Affine.Equation, Affine.polynomial, cusp, Polynomial.evalEval]

open Universal
variable {R} [CommRing R] (W : WeierstrassCurve R)

/-- The specialization homomorphism from `ℤ[A₁, ⋯, A₆]`
to the ring of definition of the Weierstrass curve. -/
def specialize : MvPolynomial Coeff ℤ →+* R :=
  (MvPolynomial.aeval <| Coeff.rec W.a₁ W.a₂ W.a₃ W.a₄ W.a₆).toRingHom

/-- Every Weierstrass curve is a specialization of the universal Weierstrass curve. -/
lemma map_specialize : Universal.curve.map W.specialize = W := by simp [specialize, curve, map]

namespace Universal

variable (x y : R)

open Polynomial (eval₂RingHom) in
/-- A point in the affine plane over `R` induces an evaluation homomorphism
from `ℤ[A₁, ⋯, A₆, X, Y]` to `R`. -/
def polyEval : Poly →+* R := eval₂RingHom (eval₂RingHom W.specialize x) y

open Polynomial in
lemma polyEval_apply (p : Poly) :
    polyEval W x y p = (p.map <| mapRingHom W.specialize).evalEval x y :=
  eval₂_eval₂RingHom_apply _ _ _ _

variable {W x y} (eqn : Affine.Equation W x y)

open Polynomial in
/-- A point on a Weierstrass curve over `R` induces a specialization homomorphism
from the universal ring to `R`. -/
def ringEval : Universal.Ring →+* R :=
  AdjoinRoot.lift (eval₂RingHom W.specialize x) y <| by
    simp_rw [← coe_eval₂RingHom, eval₂RingHom_eval₂RingHom, RingHom.comp_apply, coe_mapRingHom]
    rwa [← Affine.map_polynomial, map_specialize]

lemma ringEval_mk (p : Poly) : ringEval eqn (AdjoinRoot.mk _ p) = polyEval W x y p :=
  AdjoinRoot.lift_mk _ p

lemma ringEval_comp_mk : (ringEval eqn).comp (AdjoinRoot.mk _) = polyEval W x y :=
  RingHom.ext (ringEval_mk eqn)

lemma polyEval_comp_eq_specialize : (polyEval W x y).comp (algebraMap _ _) = W.specialize := by
  ext <;> simp [polyEval]

lemma ringEval_comp_eq_specialize : (ringEval eqn).comp (algebraMap _ _) = W.specialize := by
  rw [algebraMap_ring_eq_comp, ← RingHom.comp_assoc, ringEval_comp_mk, polyEval_comp_eq_specialize]

protected lemma Field.two_ne_zero : (2 : Universal.Field) ≠ 0 := by
  rw [← map_ofNat (algebraMap Universal.Ring _), map_ne_zero_iff _ (IsFractionRing.injective _ _)]
  intro h; replace h := congr(ringEval cusp_equation_one_one $h)
  rw [map_ofNat, map_zero] at h; cases h

lemma curveRing_map_ringEval : curveRing.map (ringEval eqn) = W :=
  (map_map curve (algebraMap _ _) (ringEval eqn)).symm ▸
    (ringEval_comp_eq_specialize eqn) ▸ map_specialize W

end Universal

end WeierstrassCurve

end

end

/-!
Ported from mathlib PR #41197, revision
`f46c499f84960839eac3fdbc517a930f02b3b252`
(https://github.com/leanprover-community/mathlib4/pull/41197).

# The omega division polynomials and related definitions

This file extends the division polynomial development from mathlib with the `ω` family of
division polynomials, the complement `ψc`, and the invariant `invar`, which are needed for
the `ZSMul` proof.

## Main definitions

 * `WeierstrassCurve.invar`: the "invariant" polynomial.
 * `WeierstrassCurve.ψc`: the complement of `ψ(n)` in `ψ(2n)`.
 * `WeierstrassCurve.ω`: the bivariate polynomials `ωₙ`.
 * `WeierstrassCurve.isEllSequence_ψ`: the `ψ` family forms an elliptic sequence.
-/

@[expose] public section
open FLT.NTorsionAux
open Polynomial
open scoped Polynomial.Bivariate

local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

local macro "map_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_neg, map_add, map_sub, map_mul, map_pow, map_div₀,
    Polynomial.map_ofNat, Polynomial.map_one, map_C, map_X, Polynomial.map_neg, Polynomial.map_add,
    Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_div, coe_mapRingHom,
    apply_ite <| mapRingHom _, WeierstrassCurve.map])

namespace WeierstrassCurve

variable {R : Type*} {S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R)

noncomputable section

open Affine (polynomial polynomialX polynomialY negPolynomial)
open EllSequence
open WeierstrassCurve (ψ₂ ψ φ)

/-- The "invariant" that is equal to the quotient
`(ψ(n-1)²ψ(n+2)+ψ(n-2)ψ(n+1)²+ψ₂²ψ(n)³)/ψ(n+1)ψ(n)ψ(n-1)` for arbitrary `n`
modulo the Weierstrass polynomial. -/
def invar : R[X] := 6 * X ^ 2 + C W.b₂ * X + C W.b₄

/-- The complement of ψ(n) in ψ(2n). -/
def ψc : ℤ → R[X][Y] := compl₂EDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄)

lemma isEllSequence_ψ : FLT.NTorsionAux.IsEllSequence W.ψ := FLT.NTorsionAux.IsEllSequence.normEDS

lemma C_Ψ₃_eq :
    C W.Ψ₃ = (3 * C X + CC W.a₂) * C W.Ψ₂Sq - polynomialX W ^ 2
      + CC W.a₁ * W.ψ₂ * polynomialX W - CC W.a₁ ^ 2 * polynomial W := by
  simp_rw [Ψ₃, Ψ₂Sq, polynomial, polynomialX, ψ₂, polynomialY, b₂, b₄, b₆, b₈, CC]; C_simp; ring

lemma preΨ₄_add_Ψ₂Sq_sq : W.preΨ₄ + W.Ψ₂Sq ^ 2 = W.invar * W.Ψ₃ := by
  rw [preΨ₄, Ψ₂Sq, invar, Ψ₃]
  linear_combination (norm := (C_simp; ring_nf)) congr(C $W.b_relation) * (@X R _) ^ 2

lemma preΨ₄_add_ψ₂_pow_four : C W.preΨ₄ + W.ψ₂ ^ 4 =
    C (W.invar * W.Ψ₃) + 8 * polynomial W * (2 * polynomial W + C W.Ψ₂Sq) := by
  simp_rw [show 4 = 2 * 2 by rfl, pow_mul, ψ₂_sq, add_sq,
    ← add_assoc, ← C_pow, ← C_add, preΨ₄_add_Ψ₂Sq_sq]; C_simp; ring

lemma φ_mul_ψ (n : ℤ) : W.φ n * W.ψ n = C X * W.ψ n ^ 3 - invarDenom W.ψ 1 n := by
  rw [φ, invarDenom]; ring

/-- The `ω` family of division polynomials: `ω n` gives the second (`Y`) coordinate in
Jacobian coordinates of the scalar multiplication by `n`. -/
protected def ω (n : ℤ) : R[X][Y] :=
  redInvarDenom W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n *
    ((CC W.a₁ * polynomialY W - polynomialX W) * C W.Ψ₃
      + 4 * polynomial W * (2 * polynomial W + C W.Ψ₂Sq))
  - compl₂EDSAux W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n + negPolynomial W * W.ψ n ^ 3

open WeierstrassCurve (ω)

lemma ψ_eq_normEDS : W.ψ = normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) := rfl

lemma ω_spec (n : ℤ) :
    2 * W.ω n + CC W.a₁ * W.φ n * W.ψ n + CC W.a₃ * W.ψ n ^ 3 = W.ψc n := by
  rw [ψc, compl₂EDS_eq_redInvarNum_sub, redInvar_normEDS, preΨ₄_add_ψ₂_pow_four, mul_assoc (C _),
    φ_mul_ψ, ψ_eq_normEDS, invarDenom_eq_redInvarDenom_mul, ω, ← ψ_eq_normEDS, invar, b₂, b₄, ψ₂,
    polynomialY, polynomialX, negPolynomial]
  C_simp; ring

lemma two_mul_ω (n : ℤ) :
    2 * W.ω n = W.ψc n - CC W.a₁ * W.φ n * W.ψ n - CC W.a₃ * W.ψ n ^ 3 := by
  rw [← ω_spec]; abel

lemma ψc_spec (n : ℤ) : W.ψ n * W.ψc n = W.ψ (2 * n) := normEDS_mul_compl₂EDS _ _ _ _

@[simp] lemma ω_zero : W.ω 0 = 1 := by simp [ω]
@[simp] lemma ω_one : W.ω 1 = Y := by simp [ω, ψ₂, ← Affine.Y_sub_polynomialY]
@[simp] lemma ψc_neg (n : ℤ) : W.ψc (-n) = W.ψc n := by simp [ψc]

end

section Map

/-! ### Maps across ring homomorphisms -/

open WeierstrassCurve (Ψ Φ ψ φ ω)

variable (f : R →+* S)

open Affine EllSequence in
@[simp]
lemma map_ω (n : ℤ) : (W.map f).ω n = (W.ω n).map (mapRingHom f) := by
  simp_rw [ω, ← coe_mapRingHom, map_add, map_sub, map_mul, map_redInvarDenom, map_compl₂EDSAux,
    map_polynomial, map_polynomialX, map_polynomialY, map_negPolynomial, map_ψ₂, map_Ψ₃, map_preΨ₄,
    map_Ψ₂Sq, map_ψ]; simp

private lemma universal_ω_neg (n : ℤ) : letI W := Universal.curve
    W.ω (-n) = W.ω n + CC W.a₁ * W.φ n * W.ψ n + CC W.a₃ * W.ψ n ^ 3 := by
  rw [← mul_cancel_left_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero Universal.Poly.two_ne_zero)]
  simp_rw [left_distrib, two_mul_ω, ψc_neg, ψ_neg, φ_neg]; ring

lemma ω_neg (n : ℤ) : W.ω (-n) = W.ω n + CC W.a₁ * W.φ n * W.ψ n + CC W.a₃ * W.ψ n ^ 3 := by
  rw [← W.map_specialize, map_ω, universal_ω_neg, map_φ, map_ω, map_ψ]; simp

end Map

end WeierstrassCurve

end

/-!
Ported from mathlib PR #41197, revision
`f46c499f84960839eac3fdbc517a930f02b3b252`
(https://github.com/leanprover-community/mathlib4/pull/41197).

# Integer multiples of a rational point on a elliptic curve in terms of division polynomials

This file proves the formula `WeierstrassCurve.zsmul_eq_smulEval`, which says that
`n • P = (φₙ(x,y) : ωₙ(x,y), ψₙ(x,y))` in Jacobian coordinates for any integer `n`
and any nonsingular rational point `P : W.Point` in affine coordinates `(x,y)`
on a Weierstrass curve `W` over a field.

It is easy to deduce the formula for `(-n) • P` from the formula for `n • P`, and the
`n = 0` and `n = 1` cases are trivially verified. The formula for `n > 1` is proved by
even-odd induction on `n`. If `n = 2 * m`, we use the doubling formula to write `n • P`
as `Jacobian.dblXYZ (m • P)`, while if `n = 2 * m + 1`, we use the addition formula to write it
as `Jacobian.addXYZ (m • P) ((m + 1) • P)`. By induction hypothesis, `m • P` and `(m + 1) • P` are
given by evaluation of division polynomials (`smulEval`), so our task reduces to proving
`dblXYZ_smulEval` and `addXYZ_smulEval₁`.

Since `dblXYZ`, `addXYZ` and the division polynomials are all compatible
with ring homomorphisms (`map_dblXYZ`, `map_addXYZ` and `map_ψ` etc.), it further
reduces to proving certain polynomial identites (`dblXYZ_smulRing` and `addXYZ_smulRing`)
of universal division polynomials (`smulRing`), because there is a homomorphism
`ringEval W (_ : Affine.Equation W x y)` from `Universal.Ring` that specialize the universal
division polynomials to their evaluations at `(x,y)` (see `ringEval_comp_smulRing`).

The polynomial identities say that `dblXYZ` and `addXYZ`, when applied to the universal
`(φₘ, ωₘ, ψₘ)` and `(φₘ₊₁, ωₘ₊₁, ψₘ₊₁)`, yields `(φ₂ₘ, ω₂ₘ, ψ₂ₘ)` and `(φ₂ₘ₊₁, ω₂ₘ₊₁, ψ₂ₘ₊₁)`,
modulo the Weierstrass polynomial. It is crucial that two formulas (`dblXYZ` for doubling,
`addXYZ` for addition of two different points) suffice to cover all cases of the group law
in Jacobian coordinates. Since `P = (x,y) ≠ O`, `m • P` is never equal to `(m + 1) • P`, so
`addXYZ` always apply in the `2 * m + 1` case (it gives `(0,0,0)` when applied to two equal points),
and `dblXYZ` always applies in the `2 * m` case. This already implies the existence of
division polynomials that are the same polynomials in `a₁, ⋯, a₆, x, y` no matter what the
field is, but not their explicit forms, which are needed to compute their degrees.

Since the ring homomorphism from the universal ring to the universal field
is injective, it suffices to prove these identities in the universal field
(`dblXYZ_smulField` and `addXYZ_smulField`), which amounts to the universal case of the identities
`dblXYZ (φₘ, ωₘ, ψₘ) = (φ₂ₘ, ω₂ₘ, ψ₂ₘ)` and
`addXYZ (φₘ, ωₘ, ψₘ) (φₘ₊₁, ωₘ₊₁, ψₘ₊₁) = (φ₂ₘ₊₁, ω₂ₘ₊₁, ψ₂ₘ₊₁)`, with `P = (X,Y)` the
universal point on the universal curve. It is easy to show the Z-coordinates are equal
even in the polynomial ring (`dblZ_smulPoly` and `addZ_smulPoly`), without passing to the quotient.

Since the universal `ψₙ` is nonzero when `n` is, to show that the other coordinates
are also equal, it suffices to show the two sides, when interpreted as Jacobian coordinates,
represent the same point on the universal curve, according to `Jacobian.equiv_iff_eq_of_Z_eq`.
If we can show the universal case of the multiplication formula `n • P = ⟦(φₘ, ωₙ, ψₙ)⟧` with
`P = (X,Y) = ⟦(X, Y, 1)⟧` (`Universal.Jacobian.zsmul_point_eq_smulField`), then the two desired
identities become `dblXYZ (m • P) = (2 * m) • P` and
`addXYZ (m • P) ((m + 1) • P) = (2 * m + 1) • P`,
which are true by the validity of the doubling and addition formulas.

Equivalently, we aim to prove the formula in affine coordinates: `n • (X,Y) = (φₘ/ψₙ², ωₙ/ψₙ³)`
for `n ≠ 0` (`Universal.Affine.zsmul_point_eq_smulX_smulY`), but this time it is easier to use
the usual strong induction on `n` rather than the even-odd induction, because we have formulas
expressing the affine coordinates of `(n+1) • P` in terms of those of `P`, `n • P` and
`(n-1) • P` (`Affine.addX_eq_addX_negY_sub`, `Affine.addY_sub_negY_addY`).
We only need to verify the base cases `n = 1` and `n = 2`, and the induction step is handled
by fancy identities of division polynomials and elliptic divisibility sequences
(`smulX_sub_sub_smulX_add`, `smulX_add` and `smulY_add_sub_negY`).

Note: it appears that if the field `F` (of which `x` and `y` are elements) is not of
characteristic 2, then we can work in the "less universal" field `Frac(F[W]) = Frac(F[X,Y]/⟨P⟩)`
instead of `Frac(Universal.Ring) = Frac(ℤ[A₁,A₂,A₃,A₄,A₆,X,Y]/⟨P⟩)`, but our argument via
`smulY_add_sub_negY` requires 2 to be invertible, so we do need to obtain the characteristic 2
result by specializing the characteristic 0, universal result.
-/

@[expose] public section
open FLT.NTorsionAux

open scoped Polynomial.Bivariate

namespace WeierstrassCurve

open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R) (f : R →+* S)

noncomputable section

variable {x y : R}

namespace Universal

lemma evalEval_ψ₂ : W.ψ₂.evalEval x y = polyEval W x y curve.ψ₂ := by
  simp_rw [polyEval_apply, ← map_ψ₂, map_specialize]

lemma evalEval_Ψ₃ : (C W.Ψ₃).evalEval x y = polyEval W x y (C curve.Ψ₃) := by
  simp_rw [polyEval_apply, map_C, coe_mapRingHom, ← map_Ψ₃, map_specialize]

lemma evalEval_preΨ₄ : (C W.preΨ₄).evalEval x y = polyEval W x y (C curve.preΨ₄) := by
  simp_rw [polyEval_apply, map_C, coe_mapRingHom, ← map_preΨ₄, map_specialize]

variable {m n : ℤ}

lemma evalEval_ψ : (W.ψ n).evalEval x y = polyEval W x y (curve.ψ n) := by
  simp_rw [polyEval_apply, ← map_ψ, map_specialize]

lemma evalEval_φ : (W.φ n).evalEval x y = polyEval W x y (curve.φ n) := by
  simp_rw [polyEval_apply, ← map_φ, map_specialize]

lemma evalEval_ω : (W.ω n).evalEval x y =  polyEval W x y (curve.ω n) := by
  simp_rw [polyEval_apply, ← map_ω, map_specialize]

open WeierstrassCurve (ψ φ ω)

lemma cusp_ψ₂ : (cusp ℤ).ψ₂ = 2 * Y := by simp [cusp, ψ₂, Affine.polynomialY, C_ofNat]
lemma cusp_Ψ₃ : (cusp ℤ).Ψ₃ = 3 * X ^ 4 := by simp [cusp, Ψ₃, b₂, b₄, b₆, b₈]
lemma cusp_preΨ₄ : (cusp ℤ).preΨ₄ = 2 * X ^ 6 := by simp [cusp, preΨ₄, b₂, b₄, b₆, b₈]

lemma polyEval_cusp_ψ : polyEval (cusp ℤ) 1 1 (curve.ψ n) = n := by
  rw [ψ, map_normEDS, ← evalEval_ψ₂, ← evalEval_Ψ₃, ← evalEval_preΨ₄, cusp_ψ₂, cusp_Ψ₃, cusp_preΨ₄]
  simp [evalEval, normEDS_two_three_two]

lemma polyEval_cusp_φ : polyEval (cusp ℤ) 1 1 (curve.φ n) = 1 := by
  simp_rw [φ, map_sub, map_mul, map_pow, polyEval_cusp_ψ, polyEval]
  simp only [coe_eval₂RingHom, eval₂_C, eval₂_X]; ring

lemma polyEval_cusp_ψc : polyEval (cusp ℤ) 1 1 (curve.ψc n) = 2 := by
  rw [ψc, map_compl₂EDS, ← evalEval_ψ₂, ← evalEval_Ψ₃, ← evalEval_preΨ₄]
  simp [cusp_ψ₂, cusp_Ψ₃, cusp_preΨ₄, evalEval, compl₂EDS_two_three_two]

lemma polyEval_cusp_ω : polyEval (cusp ℤ) 1 1 (curve.ω n) = 1 := by
  have := congr(polyEval (cusp ℤ) 1 1 $(curve.two_mul_ω n))
  simp_rw [map_sub, map_mul, map_ofNat, polyEval_cusp_ψc] at this
  simpa [cusp, polyEval, specialize, curve] using this

/-- The `ψ` family of division polynomials as elements in the universal field. -/
abbrev ψᵤ (n : ℤ) : Universal.Field := polyToField (curve.ψ n)

lemma ψᵤ_eq_normEDS :
    ψᵤ = normEDS
      (polyToField curve.ψ₂) (polyToField <| C curve.Ψ₃) (polyToField <| C curve.preΨ₄) := by
  ext; rw [← map_normEDS]; rfl

lemma isEllSequence_ψᵤ : FLT.NTorsionAux.IsEllSequence ψᵤ := by
  rw [ψᵤ_eq_normEDS]
  exact FLT.NTorsionAux.IsEllSequence.normEDS
lemma net_ψᵤ (p q r s) : EllSequence.net ψᵤ p q r s = 0 := by rw [ψᵤ_eq_normEDS]; apply net_normEDS

lemma ψᵤ_ne_zero (h0 : n ≠ 0) : ψᵤ n ≠ 0 := fun h ↦ by
  rw [ψᵤ, polyToField_apply, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h
  replace h := congr(ringEval cusp_equation_one_one $h)
  rw [ringEval_mk, polyEval_cusp_ψ, map_zero] at h
  exact h0 h

lemma polyToField_φ_ne_zero : polyToField (curve.φ n) ≠ 0 := fun h ↦ by
  rw [polyToField_apply, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h
  replace h := congr(ringEval cusp_equation_one_one $h)
  rw [ringEval_mk, polyEval_cusp_φ, map_zero] at h
  exact one_ne_zero h

lemma polyToField_ψ₂Sq : polyToField (C curve.Ψ₂Sq) = ψᵤ 2 ^ 2 := by
  rw [← map_pow, ψ_two, ψ₂_sq, map_add, map_mul, polyToField_polynomial, mul_zero, add_zero]

namespace Affine

attribute [local instance] Classical.propDecidable

variable (n)
/-- The rational function φₙ/ψₙ², which we will show to be the `X`-coordinate
of the point `n • (X, Y)` on the universal curve. -/
def smulX : Universal.Field := polyToField (curve.φ n) / (ψᵤ n) ^ 2

/-- The rational function ωₙ/ψₙ³, which we will show to be the `Y`-coordinate
of the point `n • (X, Y)` on the universal curve. -/
def smulY : Universal.Field := polyToField (curve.ω n) / (ψᵤ n) ^ 3
variable {n}

@[simp] lemma smulX_zero : smulX 0 = 0 := by simp [smulX, ψᵤ]
@[simp] lemma smulY_zero : smulY 0 = 0 := by simp [smulY, ψᵤ]
@[simp] lemma smulX_one : smulX 1 = polyToField (C X) := by simp [smulX, ψᵤ]
@[simp] lemma smulY_one : smulY 1 = polyToField Y := by simp [smulY, ψᵤ]

lemma smulX_eq (hn : n ≠ 0) :
    smulX n = smulX 1 - ψᵤ (n + 1) * ψᵤ (n - 1) / (ψᵤ n) ^ 2 := by
  rw [smulX, eq_sub_iff_add_eq]
  simp only [φ, ψᵤ, map_sub, map_mul, map_pow, ← add_div]
  rw [div_eq_iff (pow_ne_zero 2 (ψᵤ_ne_zero hn)), smulX_one]
  abel

lemma smulX_two : smulX 2 = smulX 1 - ψᵤ 3 / (ψᵤ 2) ^ 2 := by
  simp [smulX_eq two_ne_zero, ψᵤ]

lemma smulX_sub_smulX (hm : m ≠ 0) (hn : n ≠ 0) :
    smulX m - smulX n = (ψᵤ (n + m) * ψᵤ (n - m)) / (ψᵤ n * ψᵤ m) ^ 2 := by
  rw [smulX_eq hm, smulX_eq hn,
    show ∀ (c a b : Universal.Field), c - a - (c - b) = b - a from fun c a b ↦ by ring,
    div_sub_div]
  · rw [mul_pow]; congr; convert (isEllSequence_ψᵤ n m 1).symm using 1
    · ring
    · simp [ψᵤ]
  all_goals exact pow_ne_zero _ (ψᵤ_ne_zero <| by assumption)

lemma smulX_sub_sub_smulX_add (add_ne : n + m ≠ 0) (sub_ne : n - m ≠ 0) :
    smulX (n - m) - smulX (n + m) = (ψᵤ (2 * n) * ψᵤ (2 * m)) / (ψᵤ (n + m) * ψᵤ (n - m)) ^ 2 := by
  rw [smulX_sub_smulX sub_ne add_ne]
  simp only [show n + m + (n - m) = 2 * n by ring, show n + m - (n - m) = 2 * m by ring]

lemma smulX_neg : smulX (-n) = smulX n := by simp_rw [smulX, φ_neg, ψᵤ, ψ_neg, ← map_pow, neg_sq]

lemma smulX_ne_zero (h0 : n ≠ 0) : smulX n ≠ 0 :=
  div_ne_zero polyToField_φ_ne_zero (pow_ne_zero _ <| ψᵤ_ne_zero h0)

lemma smulX_ne_smulX (ne : m ≠ n) (ne_neg : m ≠ -n) : smulX m ≠ smulX n := by
  obtain rfl | hm := eq_or_ne m 0
  · rw [smulX_zero]; exact (smulX_ne_zero ne.symm).symm
  obtain rfl | hn := eq_or_ne n 0
  · rw [smulX_zero]; exact smulX_ne_zero ne
  rw [← sub_ne_zero, smulX_sub_smulX hm hn]
  rw [ne_comm, ← sub_ne_zero] at ne
  rw [Ne, ← add_eq_zero_iff_eq_neg, add_comm] at ne_neg
  refine div_ne_zero (mul_ne_zero ?_ ?_) (pow_ne_zero _ <| mul_ne_zero ?_ ?_) <;>
    apply ψᵤ_ne_zero <;> assumption

lemma smulX_eq_smulX_iff : smulX m = smulX n ↔ m = n ∨ m = -n := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · contrapose! h; exact smulX_ne_smulX h.1 h.2
  · rintro (rfl|rfl); exacts [rfl, smulX_neg]

private lemma smulY_sub_negY_aux {F} [Field F] {a₁ a₃ x y z : F} (h0 : z ≠ 0) :
    y / z ^ 3 - (-(y / z ^ 3) - a₁ * (x / z ^ 2) - a₃) =
      z * (2 * y + a₁ * x * z + a₃ * z ^ 3) / z ^ 4 := by
  field_simp; ring

lemma smulY_sub_negY (h0 : n ≠ 0) :
    smulY n - pointedCurve.toAffine.negY (smulX n) (smulY n) = ψᵤ (2 * n) / (ψᵤ n) ^ 4 := by
  simp_rw [Affine.negY, pointedCurve_a₁, pointedCurve_a₃, smulX, smulY, ψᵤ, ← ψc_spec, ← ω_spec,
    map_mul, map_add, map_mul, map_pow, map_ofNat]
  exact smulY_sub_negY_aux (ψᵤ_ne_zero h0)

lemma smulY_one_sub_negY :
    smulY 1 - pointedCurve.toAffine.negY (smulX 1) (smulY 1) = ψᵤ 2 := by
  rw [smulY_sub_negY one_ne_zero, mul_one, ψᵤ, ψᵤ, ψ_one, map_one, one_pow, div_one]

lemma smulY_one_ne_negY : smulY 1 ≠ pointedCurve.toAffine.negY (smulX 1) (smulY 1) := by
  rw [← sub_ne_zero, smulY_one_sub_negY]; exact ψᵤ_ne_zero two_ne_zero

/-- The slope of the tangent line at the point (X,Y) on the universal curve. -/
def slopeOne : Universal.Field :=
  pointedCurve.toAffine.slope (smulX 1) (smulX 1) (smulY 1) (smulY 1)

lemma slopeOne_eq_neg_div : slopeOne = -polyToField curve.polynomialX / ψᵤ 2 := by
  have hψ₂ : ψᵤ 2 ≠ 0 := ψᵤ_ne_zero two_ne_zero
  rw [slopeOne, Affine.slope_of_Y_ne rfl smulY_one_ne_negY, smulY_one_sub_negY,
    Affine.polynomialX]
  simp only [smulX_one, smulY_one, pointedCurve_a₁, pointedCurve_a₂, pointedCurve_a₄,
    map_sub, map_mul, map_pow, map_ofNat, map_add]
  rw [eq_comm, ← sub_eq_zero]; field_simp; norm_num

private lemma addX_smul_one_smul_one_aux {F} [Field F] {a₁ a₂ x dx dy : F} (h0 : dy ≠ 0) :
    (-dx / dy) ^ 2 + a₁ * (-dx / dy) - a₂ - x - x - x =
      (dx ^ 2 - a₁ * dx * dy - (3 * x + a₂) * dy ^ 2) / dy ^ 2 := by
  field_simp; ring

private lemma addX_smul_ring_identity {F} [Field F] {X' ψ a₁ a₂ cx : F} :
    X' * (X' + -(ψ * a₁)) - ψ ^ 2 * a₂ - ψ ^ 2 * cx - ψ ^ 2 * cx =
    ψ ^ 2 * cx - (ψ ^ 2 * (cx * 3 + a₂) - X' ^ 2 + X' * ψ * a₁ - a₁ ^ 2 * 0) := by ring

lemma addX_smul_one_smul_one :
    pointedCurve.toAffine.addX (smulX 1) (smulX 1) slopeOne = smulX 2 := by
  have hψ₂ : polyToField (ψ₂ curve) ≠ (0 : Universal.Field) :=
    ψ_two curve ▸ ψᵤ_ne_zero two_ne_zero
  rw [Affine.addX, slopeOne_eq_neg_div, smulX_two, smulX_one]
  simp only [pointedCurve_a₁, pointedCurve_a₂, ψᵤ, ψ_two, ψ_three, C_Ψ₃_eq,
    polyToField_ψ₂Sq, map_sub, map_add, map_mul, map_pow, map_ofNat, polyToField_polynomial]
  field_simp [hψ₂]
  exact addX_smul_ring_identity

private lemma addY_smul_one_smul_one_aux {F} [Field F] {a₁ a₃ dx dy x y ψ₃ t : F} (h0 : dy ≠ 0) :
    ((a₁ * dy - dx) * ψ₃ + 0 * t + (-y - (a₁ * x + a₃)) * dy ^ 3) / dy ^ 3 =
      -(-dx / dy * (x - ψ₃ / dy ^ 2 - x) + y) - a₁ * (x - ψ₃ / dy ^ 2) - a₃ := by
  field_simp; ring

open EllSequence in
lemma addY_smul_one_smul_one :
    pointedCurve.toAffine.addY (smulX 1) (smulX 1) (smulY 1) slopeOne = smulY 2 := .symm <| by
  rw [smulY, ω, redInvarDenom_two, one_mul, compl₂EDSAux_two, sub_zero, Affine.addY,
    Affine.negAddY, addX_smul_one_smul_one, smulX_two, Affine.negY, Affine.negPolynomial,
    slopeOne_eq_neg_div, ← ψ₂, ← ψ_two, smulX_one, smulY_one, ψᵤ, ψᵤ, ψ_three]
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, polyToField_polynomial, mul_zero,
    pointedCurve_a₁, pointedCurve_a₃]
  exact addY_smul_one_smul_one_aux (ψᵤ_ne_zero two_ne_zero)

private lemma smulY_neg_aux {F} [Field F] {a₁ a₃ x y z : F} (hz : z ≠ 0) :
    (y + a₁ * x * z + a₃ * z ^ 3) / (-z) ^ 3 = -(y / z ^ 3) - a₁ * (x / z ^ 2) - a₃ := by
  rw [neg_pow]; field_simp; ring

lemma smulY_neg (h0 : n ≠ 0) :
    smulY (-n) = pointedCurve.toAffine.negY (smulX n) (smulY n) := by
  simp only [Affine.negY, smulX, smulY, ψ_neg, ω_neg, map_add, map_neg, map_mul, map_pow, ψᵤ]
  exact smulY_neg_aux (ψᵤ_ne_zero h0)

private lemma smulX_add_aux {F} [Field F] {m n m₂ n₂ a s : F}
    (hm : m ≠ 0) (hn : n ≠ 0) (ha : a ≠ 0) (hs : s ≠ 0) :
    n₂ / n ^ 4 * (m₂ / m ^ 4) / (a * s / (n * m) ^ 2) ^ 2 = n₂ * m₂ / (a * s) ^ 2 := by
  field_simp

lemma smulX_add (hm : m ≠ 0) (hn : n ≠ 0) (add_ne : n + m ≠ 0) (sub_ne : n - m ≠ 0) :
    let ψ₂ x y := y - pointedCurve.toAffine.negY x y
    smulX (n + m) = smulX (n - m) -
      ψ₂ (smulX n) (smulY n) * ψ₂ (smulX m) (smulY m) / (smulX m - smulX n) ^ 2 := by
  change smulX (n + m) = smulX (n - m) -
    (smulY n - pointedCurve.toAffine.negY (smulX n) (smulY n)) *
    (smulY m - pointedCurve.toAffine.negY (smulX m) (smulY m)) / (smulX m - smulX n) ^ 2
  rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq']
  calc _ = ψᵤ (2 * n) / ψᵤ n ^ 4 * (ψᵤ (2 * m) / ψᵤ m ^ 4) /
      (ψᵤ (n + m) * ψᵤ (n - m) / (ψᵤ n * ψᵤ m) ^ 2) ^ 2 := by
        rw [smulY_sub_negY hm, smulY_sub_negY hn, smulX_sub_smulX hm hn]
      _ = ψᵤ (2 * n) * ψᵤ (2 * m) / (ψᵤ (n + m) * ψᵤ (n - m)) ^ 2 :=
        smulX_add_aux (ψᵤ_ne_zero hm) (ψᵤ_ne_zero hn)
          (ψᵤ_ne_zero add_ne) (ψᵤ_ne_zero sub_ne)
      _ = smulX (n - m) - smulX (n + m) :=
        (smulX_sub_sub_smulX_add add_ne sub_ne).symm

private lemma smulY_add_sub_negY_aux {F} [Field F] {m n m₂ n₂ a s am an : F}
    (hm : m ≠ 0) (hn : n ≠ 0) (ha : a ≠ 0) (hs : s ≠ 0) :
    (m₂ / m ^ 4 * (an * m / (a * n) ^ 2) - n₂ / n ^ 4 * (am * n / (a * m) ^ 2))
      / (a * s / (n * m) ^ 2)
      = (an * m₂ * n - am * n₂ * m) * a / (s * n * m) / a ^ 4 := by
  field_simp

lemma smulY_add_sub_negY (hm : m ≠ 0) (hn : n ≠ 0) (add_ne : n + m ≠ 0) (sub_ne : n - m ≠ 0) :
    let ψ₂ x y := y - pointedCurve.toAffine.negY x y
    ψ₂ (smulX (n + m)) (smulY (n + m)) =
      (ψ₂ (smulX m) (smulY m) * (smulX n - smulX (n + m))
        - ψ₂ (smulX n) (smulY n) * (smulX m - smulX (n + m))) / (smulX m - smulX n) := by
  simp_rw [smulY_sub_negY add_ne, smulY_sub_negY hm, smulY_sub_negY hn, smulX_sub_smulX hn add_ne,
    smulX_sub_smulX hm add_ne, smulX_sub_smulX hm hn, add_sub_cancel_left, add_sub_cancel_right]
  rw [smulY_add_sub_negY_aux (ψᵤ_ne_zero hm) (ψᵤ_ne_zero hn) (ψᵤ_ne_zero add_ne)
    (ψᵤ_ne_zero sub_ne)]
  congr; rw [eq_div_iff]
  · have := (EllSequence.net_add_sub_iff _ n m).mp (net_ψᵤ _ _ _ _)
    linear_combination (norm := ring_nf) this
  apply_rules [mul_ne_zero, ψᵤ_ne_zero]

open Affine.Point

open WeierstrassCurve.Affine in
instance : AddGroup ((curve.baseChange Universal.Field).toAffine.Point) := inferInstance

/-- The affine coordinates of `n • Universal.Affine.point` is given by `(smulX n, smulY n)`. -/
theorem zsmul_point_eq_smulX_smulY : n ≠ 0 →
    ∃ h : Affine.Nonsingular _ (smulX n) (smulY n), n • Affine.point = .some _ _ h := by
  induction n using Int.negInduction with
  | nat n =>
    refine n.strong_induction_on fun n ih h0 ↦ ?_
    obtain _|_|_|n := n
    · exact (h0 rfl).elim
    · simp_rw [zero_add, Nat.cast_one, one_zsmul, smulX_one, smulY_one]
      exact ⟨Affine.equation_iff_nonsingular.mp equation_point, rfl⟩
    all_goals obtain ⟨ns, eq⟩ := ih 1 (by omega) one_ne_zero
    · erw [← addX_smul_one_smul_one, ← addY_smul_one_smul_one, zero_add, add_zsmul _ 1 1, eq]
      exact ⟨Affine.nonsingular_add ns ns fun h ↦ smulY_one_ne_negY h.2,
        add_self_of_Y_ne smulY_one_ne_negY⟩
    set n2 := n + 1 + 1
    obtain ⟨ns1, eq1⟩ := ih (n + 1) (by omega) (by omega)
    obtain ⟨ns2, eq2⟩ := ih n2 (by omega) (by omega)
    have ne : smulX n2 ≠ smulX 1 := smulX_ne_smulX (by omega) (by omega)
    simp_rw [show (n + 1 : ℕ) = n2 + (-1 : ℤ) by omega, add_zsmul, neg_smul] at eq1
    let _U := pointedCurve.toAffine
    erw [eq2, eq, add_of_X_ne ne, some_eq_some_iff] at eq1
    let L := _U.slope (smulX n2) (smulX 1) (smulY n2) (smulY 1)
    have X_eq : smulX (n2 + 1 : ℕ) = _U.addX (smulX n2) (smulX 1) L := by
      rw [Nat.cast_add, Nat.cast_one, smulX_add one_ne_zero (by omega) (by omega) (by omega),
        Affine.addX_eq_addX_negY_sub _ _ ne, sub_eq_add_neg (n2 : ℤ), ← eq1.1]; rfl
    have Y_eq : smulY (n2 + 1 : ℕ) = _U.addY (smulX n2) (smulX 1) (smulY n2) L := by
      rw [← mul_cancel_left_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero Field.two_ne_zero),
        ← add_right_cancel_iff (a := _U.a₁ * smulX (n2 + 1 : ℕ) + _U.a₃)]
      convert smulY_add_sub_negY (n := n2) one_ne_zero (by omega) (by omega) (by omega) using 1
      · simp_rw [Affine.negY, Nat.cast_add]; norm_cast
        simp only [_U, two_mul]; abel
      convert _U.addY_sub_negY_addY (smulY n2) (smulY 1) ne using 1
      · rw [Affine.negY, ← X_eq]; ring
      · rw [← X_eq]; rfl
    rw [X_eq, Y_eq, n2.cast_add, add_zsmul, eq, eq2]
    exact ⟨Affine.nonsingular_add ns2 ns (fun h ↦ ne h.1), add_of_X_ne ne⟩
  | neg ih n =>
    rw [neg_ne_zero]; intro h0
    obtain ⟨ns, eq⟩ := ih n h0
    simp_rw [smulX_neg, smulY_neg h0, neg_smul, eq, neg_some]
    exact ⟨(Affine.nonsingular_neg ..).mpr ns, trivial⟩

lemma nonsingular_smulX_smulY (hn : n ≠ 0) : Affine.Nonsingular curveField (smulX n) (smulY n) :=
  (zsmul_point_eq_smulX_smulY hn).1

/-- The distinguished point `(X,Y)` on the universal curve is not torsion. -/
lemma zsmul_point_ne_zero (h0 : n ≠ 0) : n • Affine.point ≠ 0 := by
  obtain ⟨ns, eq⟩ := zsmul_point_eq_smulX_smulY h0
  rw [eq]; exact Affine.Point.some_ne_zero ns

end Affine

namespace Jacobian

attribute [local instance] Classical.propDecidable

open WeierstrassCurve.Jacobian

open Point in
lemma zsmul_point_ne_zero (h0 : n ≠ 0) : n • Jacobian.point ≠ 0 := by
  rw [Jacobian.point, ← toAffineAddEquiv_symm_apply, ← map_zsmul (toAffineAddEquiv _).symm,
    Ne, map_eq_zero_iff _ (toAffineAddEquiv _).symm.injective]
  exact Affine.zsmul_point_ne_zero h0

lemma zsmul_point_ne (h : m ≠ n) : m • Jacobian.point ≠ n • Jacobian.point := by
  rw [← sub_ne_zero, sub_eq_add_neg, ← sub_zsmul]
  exact zsmul_point_ne_zero (sub_ne_zero.mpr h)

lemma point_point : Jacobian.point.point = ⟦![polyToField (C X), polyToField Y, 1]⟧ := rfl

/-- The three families of universal division polynomials as a 3-tuple. -/
abbrev smulPoly (n : ℤ) : Fin 3 → Poly := ![curve.φ n, curve.ω n, curve.ψ n]
/-- The three families of division polynomials as elements in the universal ring. -/
abbrev smulRing (n : ℤ) : Fin 3 → Universal.Ring := AdjoinRoot.mk _ ∘ smulPoly n
/-- The three families of division polynomials as elements in the universal field. -/
abbrev smulField (n : ℤ) : Fin 3 → Universal.Field := polyToField ∘ smulPoly n

lemma algebraMap_comp_smulRing (n : ℤ) : algebraMap _ _ ∘ smulRing n = smulField n := by
  ext i; fin_cases i <;> rfl

/-- The Jacobian coordinates of `n • Universal.Jacobian.point` is given by `smulField n`. -/
theorem zsmul_point_eq_smulField : (n • Jacobian.point).point = ⟦smulField n⟧ := by
  rw [← fin3_def (smulField n), smulField, smulPoly]
  simp_rw [Function.comp, fin3_def_ext]
  obtain rfl | hn := eq_or_ne n 0
  · simp_rw [zero_zsmul, φ_zero, ω_zero, ψ_zero, map_zero, map_one]; rfl
  obtain ⟨ns, eq⟩ := Affine.zsmul_point_eq_smulX_smulY hn
  change (n • (Point.toAffineAddEquiv _).symm Affine.point).point = _
  rw [← map_zsmul, eq]
  have := ψᵤ_ne_zero hn
  refine Quotient.sound ⟨.mk0 _ (inv_ne_zero this), ?_⟩
  simp_rw [Units.smul_def, Jacobian.smul_fin3]
  ext i; fin_cases i <;> simp [Affine.smulX, Affine.smulY, this, inv_mul_eq_div]

lemma dblZ_smulPoly : dblZ curvePoly (smulPoly n) = curve.ψ (2 * n) := by
  unfold dblZ smulPoly WeierstrassCurve.Jacobian.negY curvePoly
    WeierstrassCurve.Affine.baseChange WeierstrassCurve.baseChange
  simp_rw [fin3_def_ext, WeierstrassCurve.map]
  rw [← ψc_spec _ n]; congr; convert curve.ω_spec n using 1
  simp_rw [show ∀ x, CC x = (algebraMap _ Poly) x from fun _ ↦ rfl]
  norm_num; ring

lemma nonsingular_smulField : Nonsingular curveField (smulField n) := by
  rw [← nonsingularLift_iff]
  simpa only [zsmul_point_eq_smulField] using (n • Jacobian.point).nonsingular

private lemma two_zsmul_point_eq_dblXYZ {P : Point (baseChange curve Universal.Field)}
    {v : Fin 3 → Universal.Field} (hv : P.point = ⟦v⟧) :
    ((2 : ℤ) • P).point = ⟦dblXYZ curveField v⟧ := by
  rw [two_zsmul, Point.add_point, hv, addMap_eq, add_self]

private lemma add_point_of_ne_eq_addXYZ {P Q : Point (baseChange curve Universal.Field)}
    {v w : Fin 3 → Universal.Field} (hv : P.point = ⟦v⟧) (hw : Q.point = ⟦w⟧) (hne : P ≠ Q) :
    (P + Q).point = ⟦addXYZ curveField v w⟧ := by
  rw [Point.add_point, hv, hw, addMap_eq, add_of_not_equiv]
  intro h; exact hne (Point.ext_iff.mpr (hv ▸ hw ▸ Quotient.eq.mpr h))

lemma dblXYZ_smulField : dblXYZ curveField (smulField n) = smulField (2 * n) := by
  obtain rfl | hn := eq_or_ne n 0
  · simp only [mul_zero, smulField, smulPoly, comp_fin3]
    simp only [dblXYZ, dblX, dblY, dblZ, dblU_eq, negY, negDblY, curveField, fin3_def_ext]
    ext i; fin_cases i <;> simp [fin3_def_ext] <;> norm_num
  refine (equiv_iff_eq_of_Z_eq ?_ (ψᵤ_ne_zero <| mul_ne_zero two_ne_zero hn)).mp
    (Quotient.exact ?_)
  · simp only [smulField, smulPoly, fin3_def_ext, Function.comp, ← dblZ_smulPoly, ← map_dblZ]; rfl
  · exact (two_zsmul_point_eq_dblXYZ zsmul_point_eq_smulField).symm.trans <|
      (congrArg Point.point (mul_zsmul _ 2 n).symm).trans zsmul_point_eq_smulField

lemma dblXYZ_smulRing : dblXYZ curveRing (smulRing n) = smulRing (2 * n) :=
  (IsFractionRing.injective _ Universal.Field).comp_left <| by
    simp_rw [← map_dblXYZ]; exact dblXYZ_smulField

lemma addZ_smulPoly : addZ (smulPoly m) (smulPoly n) = curve.ψ (n + m) * curve.ψ (n - m) := by
  simp_rw [addZ, smulPoly, φ]; convert (curve.isEllSequence_ψ n m 1).symm using 1
  · simp only [fin3_def_ext]; ring
  · rw [ψ_one]; ring

lemma ω_neg_eq_neg_negY : curve.ω (-n) = -negY curvePoly (smulPoly n) := by
  unfold smulPoly WeierstrassCurve.Jacobian.negY curvePoly
    WeierstrassCurve.Affine.baseChange WeierstrassCurve.baseChange
  simp_rw [ω_neg, fin3_def_ext, WeierstrassCurve.map,
    show ∀ x, CC x = (algebraMap _ Poly) x from fun _ ↦ rfl]
  norm_num; ring

lemma smulPoly_neg : smulPoly (-n) = (-1 : Poly) • neg curvePoly (smulPoly n) := by
  simp [smulPoly, ω_neg_eq_neg_negY, neg, smul_fin3, (show Odd 3 by decide).neg_pow]

lemma smulRing_neg : smulRing (-n) = (-1 : Universal.Ring) • neg curveRing (smulRing n) := by
  simp_rw [smulRing, smulPoly_neg, Jacobian.comp_smul, ← Jacobian.map_neg, map_neg, map_one]; rfl

lemma smulField_neg : smulField (-n) = (-1 : Universal.Field) • neg curveField (smulField n) := by
  simp_rw [smulField, smulPoly_neg, Jacobian.comp_smul, ← Jacobian.map_neg, map_neg, map_one]; rfl

lemma smulPoly_zero : smulPoly 0 = ![1, 1, 0] := by simp [smulPoly]
lemma smulField_zero : smulField 0 = ![1, 1, 0] := by simp [smulField, smulPoly_zero, comp_fin3]

lemma addXYZ_smulField :
    addXYZ curveField (smulField m) (smulField n) =
      polyToField (curve.ψ (n - m)) • smulField (n + m) := by
  obtain rfl | h := eq_or_ne m n
  · rw [sub_self, ψ_zero, map_zero, smul_fin3,
      addXYZ_self nonsingular_smulField.1, zero_pow two_ne_zero, zero_pow (by decide)]
    simp_rw [zero_mul]
  obtain rfl | ne_neg := eq_or_ne n (-m)
  · have jac_one_smul : ∀ (P : Fin 3 → Universal.Field), (1 : Universal.Field) • P = P :=
      fun _ ↦ by simp only [smul_fin3, one_pow, one_mul, fin3_def]
    rw [← jac_one_smul (smulField m), smulField_neg, neg_add_cancel,
      addXYZ_smul, one_mul, neg_one_sq (R := Universal.Field), addXYZ_neg nonsingular_smulField.1,
      jac_one_smul, show (-m - m : ℤ) = -(2 * m) by ring,
      ψ_neg, map_neg, ← dblZ_smulPoly, ← map_dblZ, smulField_zero]
    rfl
  refine (equiv_iff_eq_of_Z_eq ?_ ?_).mp (Quotient.exact ?_)
  · conv_rhs => rw [smulField, comp_fin3, smul_fin3, (fin3_def_ext _ _ _).2.2, mul_comm]
    simp_rw [addXYZ, fin3_def_ext, ← map_mul, ← addZ_smulPoly, ← map_addZ]
  · simp only [smul_fin3, fin3_def_ext]
    apply mul_ne_zero <;> apply ψᵤ_ne_zero <;> omega
  · rw [smul_eq _ (ψᵤ_ne_zero <| sub_ne_zero_of_ne h.symm).isUnit,
      ← zsmul_point_eq_smulField, add_comm, add_zsmul,
      add_point_of_ne_eq_addXYZ zsmul_point_eq_smulField zsmul_point_eq_smulField
        (zsmul_point_ne h)]

lemma addXYZ_smulRing :
    addXYZ curveRing (smulRing m) (smulRing n) =
      AdjoinRoot.mk curve.polynomial (curve.ψ (n - m)) • smulRing (n + m) :=
  (IsFractionRing.injective Universal.Ring Universal.Field).comp_left <| by
    simp_rw [← map_addXYZ, Jacobian.comp_smul]; exact addXYZ_smulField

lemma addXYZ_smulField₁ :
    addXYZ curveField (smulField n) (smulField (n + 1)) = smulField (2 * n + 1) := by
  rw [addXYZ_smulField, add_sub_cancel_left, ψ_one, map_one,
    show (1 : Universal.Field) • smulField (n + 1 + n) = smulField (n + 1 + n) by
      simp only [smul_fin3, one_pow, one_mul, fin3_def]]
  congr 1; omega

lemma addXYZ_smulRing₁ :
    addXYZ curveRing (smulRing n) (smulRing (n + 1)) = smulRing (2 * n + 1) := by
  rw [addXYZ_smulRing, add_sub_cancel_left, ψ_one, map_one,
    show (1 : Universal.Ring) • smulRing (n + 1 + n) = smulRing (n + 1 + n) by
      simp only [smul_fin3, one_pow, one_mul, fin3_def]]
  congr 1; omega

end Jacobian

end Universal

variable (x y) in
/-- The evaluation of the division polynomials at a point `(x,y)`, equal to the
Jacobian coordinates of `n • (x,y)` (see `smul_eq_divisionPolynomial_eval`). -/
abbrev smulEval (n : ℤ) : Fin 3 → R := evalEval x y ∘ ![W.φ n, W.ω n, W.ψ n]

variable {W} (eqn : W.toAffine.Equation x y)

open Universal Jacobian

lemma ringEval_comp_smulRing (n : ℤ) : ringEval eqn ∘ smulRing n = smulEval W x y n := by
  conv_rhs => rw [smulEval, ← W.map_specialize, map_φ, map_ω, map_ψ, ← coe_mapRingHom,
    ← Jacobian.comp_fin3, ← Function.comp_assoc, ← smulPoly, ← coe_evalEvalRingHom,
    ← RingHom.coe_comp, ← eval₂RingHom_eval₂RingHom]
  rw [smulRing, ← Function.comp_assoc, ← RingHom.coe_comp, ringEval_comp_mk, polyEval]

lemma ringEval_ψ (n : ℤ) :
    ringEval eqn (AdjoinRoot.mk _ <| curve.ψ n) = evalEval x y (W.ψ n) :=
  congr_fun (ringEval_comp_smulRing eqn n) 2

include eqn in
lemma dblXYZ_smulEval (n : ℤ) : dblXYZ W (smulEval W x y n) = smulEval W x y (2 * n) := by
  simp_rw [← ringEval_comp_smulRing eqn, ← dblXYZ_smulRing, ← map_dblXYZ, curveRing_map_ringEval]

include eqn in
lemma addXYZ_smulEval (m n : ℤ) :
    addXYZ W (smulEval W x y m) (smulEval W x y n) =
      evalEval x y (W.ψ (n - m)) • smulEval W x y (n + m) := by
  simp_rw [← ringEval_comp_smulRing eqn, ← ringEval_ψ eqn]
  rw [← Jacobian.comp_smul, ← addXYZ_smulRing, ← map_addXYZ]
  simp_rw [curveRing_map_ringEval]

include eqn in
lemma addXYZ_smulEval₁ (n : ℤ) :
    addXYZ W (smulEval W x y n) (smulEval W x y (n + 1)) = smulEval W x y (2 * n + 1) := by
  simp_rw [← ringEval_comp_smulRing eqn, ← addXYZ_smulRing₁, ← map_addXYZ, curveRing_map_ringEval]

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

open Universal

/-- The integer multiples of a nonsingular rational point `(x,y)` on a Weierstrass curve
is given by `smulEval` in Jacobian coordinates. -/
theorem zsmul_eq_smulEval {x y : F} (h : Affine.Nonsingular W x y) (n : ℤ) :
    (n • Point.fromAffine (Affine.Point.some _ _ h)).point = ⟦smulEval W x y n⟧ := by
  induction n using Int.negInduction with
  | nat n =>
    refine n.strong_induction_on fun n ih ↦ ?_
    obtain _|_|n := n
    · rw [Nat.cast_zero, zero_smul, smulEval, comp_fin3]; congrm(⟦?_⟧); simp [evalEval]
    · rw [Nat.cast_one, one_smul, smulEval, comp_fin3]; congrm(⟦?_⟧); simp [evalEval]
    obtain ⟨n, rfl|rfl⟩ := n.even_or_odd'
    · rw [show (2 * n + 1 + 1 : ℕ) = 2 * (n + 1) by omega]
      rw [Nat.cast_mul, mul_smul, natCast_zsmul, two_nsmul,
        Point.add_point, ih _ (by omega), addMap_eq, add_self,
        dblXYZ_smulEval h.1]; rfl
    · rw [show 2 * n + 1 + 1 + 1 = (n + 1) + (n + 1 + 1) by omega, Nat.cast_add, add_smul]
      have hne : (↑(n + 1) : ℤ) • Point.fromAffine (Affine.Point.some _ _ h) ≠
          (↑(n + 1 + 1) : ℤ) • Point.fromAffine (Affine.Point.some _ _ h) := by
        rw [ne_comm, ← sub_ne_zero, ← sub_smul]
        push_cast
        simp only [add_sub_cancel_left, one_smul]
        exact Point.fromAffine_some_ne_zero h
      rw [Point.add_point, ih (n + 1) (by omega), ih (n + 1 + 1) (by omega), addMap_eq,
        add_of_not_equiv (by
          intro hequiv
          exact hne (Point.ext_iff.mpr ((ih (n + 1) (by omega)) ▸ (ih (n + 1 + 1) (by omega)) ▸
            Quotient.eq.mpr hequiv)))]
      have : (↑(n + 1 + 1) : ℤ) = ↑(n + 1) + 1 := by push_cast; omega
      rw [this, addXYZ_smulEval₁ h.1]
      congrm(⟦W.smulEval x y ↑(?_)⟧); omega
  | neg ih n =>
    simp_rw [_root_.neg_smul, Point.neg_point, ih n, eq_comm]
    refine Quotient.sound ⟨-1, ?_⟩
    simp_rw [← ringEval_comp_smulRing h.1, smulRing_neg, Jacobian.comp_smul, ← Jacobian.map_neg,
      curveRing_map_ringEval, map_neg, map_one]
    rfl

end

end WeierstrassCurve

end

/-! ## Nonvanishing and finiteness over arbitrary fields -/

@[expose] public section

open Polynomial WeierstrassCurve
open scoped Polynomial.Bivariate
namespace WeierstrassCurve
variable {k : Type*} [Field k] (E : WeierstrassCurve k)
variable {x y : k} (h : E.toAffine.Equation x y)
noncomputable def pointEval : E.toAffine.CoordinateRing →+* k :=
  AdjoinRoot.evalEval h
lemma pointEval_mk (p : k[X][Y]) :
    E.pointEval h (Affine.CoordinateRing.mk E p) = p.evalEval x y := by
  exact AdjoinRoot.evalEval_mk _ p
include h in
lemma eval_ΨSq (n : ℤ) : (E.ΨSq n).eval x = ((E.ψ n).evalEval x y) ^ 2 := by
  have he := congrArg (E.pointEval h) (Affine.CoordinateRing.mk_Ψ_sq (W := E) n)
  have hψ := congrArg (E.pointEval h) (Affine.CoordinateRing.mk_ψ (W := E) n)
  simp only [map_pow, pointEval_mk, evalEval_C] at he hψ
  rw [← hψ] at he
  exact he.symm
include h in
lemma eval_Φ (n : ℤ) : (E.Φ n).eval x = (E.φ n).evalEval x y := by
  have he := congrArg (E.pointEval h) (Affine.CoordinateRing.mk_φ (W := E) n)
  simpa only [pointEval_mk, evalEval_C] using he.symm

lemma exists_equation [IsAlgClosed k] (x : k) : ∃ y, E.toAffine.Equation x y := by
  let p := E.toAffine.polynomial.map (evalRingHom x)
  have hm : p.Monic := Affine.monic_polynomial.map (evalRingHom x)
  have hd : p.natDegree = 2 :=
    (Affine.monic_polynomial.natDegree_map _).trans Affine.natDegree_polynomial
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root p (by
    rw [degree_eq_natDegree hm.ne_zero, hd]
    norm_num)
  exact ⟨y, by simpa [p, Polynomial.IsRoot, eval_map, eval₂_evalRingHom, Affine.Equation] using hy⟩

/-- The evaluated division polynomials represent a nonsingular point. -/
lemma nonsingular_smulEval {x y : k} (h : E.toAffine.Nonsingular x y) (n : ℤ) :
    E.toJacobian.Nonsingular (E.smulEval x y n) := by
  classical
  have hs := (n • Jacobian.Point.fromAffine (Affine.Point.some x y h)).nonsingular
  rwa [E.zsmul_eq_smulEval h n] at hs

variable [E.IsElliptic]

private lemma ΨSq_ne_zero_of_isAlgClosed [IsAlgClosed k] {n : ℤ} (hn : n ≠ 0) :
    E.ΨSq n ≠ 0 := by
  intro hz
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (E.Φ n)
    (by
      rw [degree_eq_natDegree (E.Φ_ne_zero n), E.natDegree_Φ n]
      exact_mod_cast pow_ne_zero 2 (Int.natAbs_ne_zero.mpr hn))
  obtain ⟨y, hy⟩ := E.exists_equation x
  have hns : E.toAffine.Nonsingular x y := E.toAffine.equation_iff_nonsingular.mp hy
  have hψ : (E.ψ n).evalEval x y = 0 := eq_zero_of_pow_eq_zero (by
    rw [← E.eval_ΨSq hy n, hz, eval_zero])
  have hφ : (E.φ n).evalEval x y = 0 := by
    rw [← E.eval_Φ hy n]
    exact hx
  have hs := E.nonsingular_smulEval hns n
  have hunit := Jacobian.isUnit_X_of_Z_eq_zero hs
    (by simpa [smulEval] using hψ)
  exact hunit.ne_zero (by simpa [smulEval] using hφ)

/-- The square division polynomial of an elliptic curve is nonzero for every nonzero
integer, including integers divisible by the characteristic. -/
lemma ΨSq_ne_zero_of_isElliptic {n : ℤ} (hn : n ≠ 0) : E.ΨSq n ≠ 0 := by
  have he := ΨSq_ne_zero_of_isAlgClosed (E.map (algebraMap k (AlgebraicClosure k))) hn
  intro hz
  apply he
  rw [map_ΨSq, hz, Polynomial.map_zero]

omit [E.IsElliptic] in
/-- The x-coordinate of a nonzero point killed by `n` is a root of `ΨSq n`. -/
lemma isRoot_ΨSq_of_nsmul_eq_zero [DecidableEq k] {x y : k}
    (h : E.toAffine.Nonsingular x y) (n : ℕ)
    (hn : n • Affine.Point.some x y h = 0) : (E.ΨSq n).IsRoot x := by
  have hj : (n : ℤ) • Jacobian.Point.fromAffine (Affine.Point.some x y h) = 0 := by
    have he := congrArg (Jacobian.Point.toAffineAddEquiv E.toJacobian).symm hn
    simpa only [map_nsmul, map_zero, natCast_zsmul,
      Jacobian.Point.toAffineAddEquiv_symm_apply] using he
  have he := (E.zsmul_eq_smulEval h (n : ℤ)).symm
  rw [hj, Jacobian.Point.zero_point] at he
  have hz := (Jacobian.Z_eq_zero_of_equiv (Quotient.exact he)).mpr rfl
  have hψ : (E.ψ n).evalEval x y = 0 := by simpa [smulEval] using hz
  change (E.ΨSq n).eval x = 0
  rw [E.eval_ΨSq h.1 n, hψ, zero_pow two_ne_zero]

/-- The kernel of multiplication by a positive integer on an elliptic curve is finite. -/
lemma finite_setOf_nsmul_eq_zero [DecidableEq k] {n : ℕ} (hn : 0 < n) :
    {P : E.toAffine.Point | n • P = 0}.Finite := by
  have hp : E.ΨSq n ≠ 0 := E.ΨSq_ne_zero_of_isElliptic (by exact_mod_cast hn.ne')
  have hf : {P : E.toAffine.Point | (E.ΨSq n).IsRoot (P.xRep 0)}.Finite :=
    (Polynomial.finite_setOfPred_isRoot hp).preimage'
      (fun x _ => Affine.finite_preimage_xRep0 x)
  apply (hf.union (Set.finite_singleton 0)).subset
  intro P hP
  cases P with
  | zero => exact Or.inr rfl
  | some x y h => exact Or.inl (E.isRoot_ΨSq_of_nsmul_eq_zero h n hP)

end WeierstrassCurve

end
