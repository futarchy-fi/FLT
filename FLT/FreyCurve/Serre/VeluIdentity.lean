/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluDifferential
public import Mathlib.FieldTheory.RatFunc.Degree

/-!
# The rational identity in Vélu's formula

The pole contributions admit expansions through order two at infinity, with
strictly lower-degree remainders. The resulting cubic residual has negative
degree. Since its formal derivative vanishes, it is constant in characteristic
zero, and the negative degree forces it to vanish.

The final identity uses exactly the coefficients t and w of the candidate curve.
Evaluation at affine points, nonsingularity, and additivity are separate steps.
-/

@[expose] public section

open scoped Polynomial BigOperators
namespace RatFunc
variable {K : Type*} [Field K]

/-- A degree bound which also includes the zero rational function. -/
def DegreeLE (f : K⟮X⟯) (n : ℤ) : Prop := f = 0 ∨ f.intDegree ≤ n

/-- A degree bound can be weakened. -/
theorem DegreeLE.mono {f : K⟮X⟯} {m n : ℤ} (h : DegreeLE f m) (hmn : m ≤ n) :
    DegreeLE f n := h.imp_right (fun hf => hf.trans hmn)

/-- The zero function satisfies every degree bound. -/
theorem DegreeLE.zero (n : ℤ) : DegreeLE (0 : K⟮X⟯) n := Or.inl rfl

/-- A constant has degree at most zero. -/
theorem DegreeLE.C (c : K) : DegreeLE (RatFunc.C c) 0 :=
  Or.inr (by simp)

/-- A natural-number constant has degree at most zero. -/
theorem DegreeLE.natCast (n : ℕ) : DegreeLE (n : K⟮X⟯) 0 := by
  simpa only [map_natCast] using DegreeLE.C (n : K)

/-- The indeterminate has degree at most one. -/
theorem DegreeLE.X : DegreeLE (RatFunc.X : K⟮X⟯) 1 := Or.inr (by simp)

/-- Negation preserves a degree bound. -/
theorem DegreeLE.neg {f : K⟮X⟯} {n : ℤ} (h : DegreeLE f n) : DegreeLE (-f) n := by
  rcases h with h | h
  · exact Or.inl (by simp [h])
  · exact Or.inr (by simpa using h)

/-- A sum preserves a common degree bound. -/
theorem DegreeLE.add {f g : K⟮X⟯} {n : ℤ}
    (hf : DegreeLE f n) (hg : DegreeLE g n) : DegreeLE (f + g) n := by
  rcases hf with rfl | hf
  · simpa using hg
  rcases hg with rfl | hg
  · exact Or.inr (by simpa using hf)
  by_cases hfg : f + g = 0
  · exact Or.inl hfg
  by_cases hg0 : g = 0
  · exact Or.inr (by simpa [hg0] using hf)
  exact Or.inr ((intDegree_add_le hg0 hfg).trans (max_le hf hg))

/-- A difference preserves a common degree bound. -/
theorem DegreeLE.sub {f g : K⟮X⟯} {n : ℤ}
    (hf : DegreeLE f n) (hg : DegreeLE g n) : DegreeLE (f - g) n := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- Degree bounds add under multiplication. -/
theorem DegreeLE.mul {f g : K⟮X⟯} {m n : ℤ}
    (hf : DegreeLE f m) (hg : DegreeLE g n) : DegreeLE (f * g) (m + n) := by
  rcases hf with rfl | hf
  · exact Or.inl (zero_mul _)
  rcases hg with rfl | hg
  · exact Or.inl (mul_zero _)
  by_cases hfg : f * g = 0
  · exact Or.inl hfg
  exact Or.inr (by rw [intDegree_mul (mul_ne_zero_iff.mp hfg).1
    (mul_ne_zero_iff.mp hfg).2]; exact add_le_add hf hg)

/-- A degree bound scales under natural powers. -/
theorem DegreeLE.pow {f : K⟮X⟯} {n : ℤ} (hf : DegreeLE f n) (k : ℕ) :
    DegreeLE (f ^ k) (n * k) := by
  induction k with
  | zero => simpa using DegreeLE.natCast (K := K) 1
  | succ k ih =>
    simpa [pow_succ, mul_add] using ih.mul hf

/-- A finite sum preserves a uniform degree bound. -/
theorem DegreeLE.sum {ι : Type*} (S : Finset ι) (f : ι → K⟮X⟯) (n : ℤ)
    (h : ∀ i ∈ S, DegreeLE (f i) n) : DegreeLE (∑ i ∈ S, f i) n := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using DegreeLE.zero (K := K) n
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i S)).add
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

/-- A simple pole contribution has degree at most minus one. -/
theorem DegreeLE.inv_X_sub_C (u : K) :
    DegreeLE ((RatFunc.X - RatFunc.C u)⁻¹ : K⟮X⟯) (-1) := by
  right
  rw [intDegree_inv]
  have h : (RatFunc.X - RatFunc.C u).intDegree = 1 := by
    rw [← algebraMap_X, ← algebraMap_C, ← map_sub, intDegree_polynomial]
    simp
  rw [h]

/-- The reciprocal indeterminate has degree at most minus one. -/
theorem DegreeLE.inv_X : DegreeLE ((RatFunc.X : K⟮X⟯)⁻¹) (-1) := by
  simpa using DegreeLE.inv_X_sub_C (0 : K)

/-- A constant of negative degree is zero. -/
theorem DegreeLE.const_eq_zero {c : K} (h : DegreeLE (RatFunc.C c) (-1)) : c = 0 := by
  rcases h with h | h
  · exact (RatFunc.C : K →+* K⟮X⟯).injective (h.trans (map_zero _).symm)
  · simp at h

/-- Multiplication by a coefficient preserves a degree bound. -/
theorem DegreeLE.const_mul {f : K⟮X⟯} {n : ℤ} (hf : DegreeLE f n) (c : K) :
    DegreeLE (RatFunc.C c * f) n := by
  simpa using (DegreeLE.C c).mul hf

/-- Division by a power of the indeterminate lowers the degree bound. -/
theorem DegreeLE.div_X_pow {f : K⟮X⟯} {n : ℤ} (hf : DegreeLE f n) (k : ℕ) :
    DegreeLE (f / RatFunc.X ^ k) (n - k) := by
  simpa [div_eq_mul_inv, sub_eq_add_neg] using hf.mul (DegreeLE.inv_X.pow k)

/-- Division by a shifted power lowers the degree bound. -/
theorem DegreeLE.div_X_sub_C_pow {f : K⟮X⟯} {n : ℤ}
    (hf : DegreeLE f n) (u : K) (k : ℕ) :
    DegreeLE (f / (RatFunc.X - RatFunc.C u) ^ k) (n - k) := by
  simpa [div_eq_mul_inv, sub_eq_add_neg] using hf.mul ((DegreeLE.inv_X_sub_C u).pow k)

open WeierstrassCurve.Velu

/-- Each pole contribution has degree at most minus one. -/
theorem degreeLE_polePart (a c u : K) :
    DegreeLE (polePart (C a) (C c) (C u) X) (-1) := by
  unfold polePart
  apply DegreeLE.add
  · simpa using (DegreeLE.C c).div_X_sub_C_pow u 1
  · exact ((DegreeLE.C a).div_X_sub_C_pow u 2).mono (by norm_num)

/-- Each slope contribution has degree at most minus two. -/
theorem degreeLE_poleSlope (a c u : K) :
    DegreeLE (poleSlope (C a) (C c) (C u) X) (-2) := by
  unfold poleSlope
  have h2a : DegreeLE (2 * C a : K⟮X⟯) 0 := by
    simpa using (DegreeLE.natCast 2).mul (DegreeLE.C a)
  exact ((DegreeLE.C c).neg.div_X_sub_C_pow u 2).sub
    ((h2a.div_X_sub_C_pow u 3).mono (by norm_num))

/-- The x-contribution expanded through order two at infinity. -/
theorem polePart_expansion (a c u : K) :
    polePart (C a) (C c) (C u) X - C c / X - (C c * C u + C a) / X ^ 2 =
      C c * C u ^ 2 / X ^ 2 / (X - C u) +
        C a * C u * (2 * X - C u) / X ^ 2 / (X - C u) ^ 2 := by
  have hx := X_ne_zero (K := K)
  have hu := X_sub_C_ne_zero u
  dsimp [polePart]
  field_simp
  ring

/-- The remainder after the first two terms has degree at most minus three. -/
theorem degreeLE_polePart_remainder (a c u : K) :
    DegreeLE
      (polePart (C a) (C c) (C u) X - C c / X - (C c * C u + C a) / X ^ 2) (-3) := by
  rw [polePart_expansion]
  have hc : DegreeLE (C c * C u ^ 2 : K⟮X⟯) 0 := by
    simpa using (DegreeLE.C c).mul ((DegreeLE.C u).pow 2)
  have hl : DegreeLE (2 * X - C u : K⟮X⟯) 1 := by
    apply DegreeLE.sub
    · simpa using (DegreeLE.natCast 2).mul (DegreeLE.X (K := K))
    · exact (DegreeLE.C u).mono (by norm_num)
  have ha : DegreeLE (C a * C u * (2 * X - C u) : K⟮X⟯) 1 := by
    simpa only [mul_assoc, Nat.cast_ofNat] using (hl.const_mul u).const_mul a
  apply DegreeLE.add
  · simpa using (hc.div_X_pow 2).div_X_sub_C_pow u 1
  · simpa using (ha.div_X_pow 2).div_X_sub_C_pow u 2

/-- The slope contribution expanded through order three at infinity. -/
theorem poleSlope_expansion (a c u : K) :
    poleSlope (C a) (C c) (C u) X + C c / X ^ 2 +
        2 * (C c * C u + C a) / X ^ 3 =
      -(C c * C u ^ 2 * (3 * X - 2 * C u) / X ^ 3 / (X - C u) ^ 2) -
        2 * C a * C u * (3 * X ^ 2 - 3 * X * C u + C u ^ 2) /
          X ^ 3 / (X - C u) ^ 3 := by
  have hx := X_ne_zero (K := K)
  have hu := X_sub_C_ne_zero u
  dsimp [poleSlope]
  field_simp
  ring

/-- The slope remainder has degree at most minus four. -/
theorem degreeLE_poleSlope_remainder (a c u : K) :
    DegreeLE
      (poleSlope (C a) (C c) (C u) X + C c / X ^ 2 +
        2 * (C c * C u + C a) / X ^ 3) (-4) := by
  rw [poleSlope_expansion]
  have hl : DegreeLE (3 * X - 2 * C u : K⟮X⟯) 1 := by
    apply DegreeLE.sub
    · simpa using (DegreeLE.natCast 3).mul (DegreeLE.X (K := K))
    · exact ((DegreeLE.natCast 2).mul (DegreeLE.C u)).mono (by norm_num)
  have hc : DegreeLE (C c * C u ^ 2 * (3 * X - 2 * C u) : K⟮X⟯) 1 := by
    simpa [mul_assoc] using ((DegreeLE.C c).mul ((DegreeLE.C u).pow 2)).mul hl
  have hquad : DegreeLE (3 * X ^ 2 - 3 * X * C u + C u ^ 2 : K⟮X⟯) 2 := by
    have h1 : DegreeLE (3 * X ^ 2 : K⟮X⟯) 2 := by
      simpa using (DegreeLE.natCast 3).mul (DegreeLE.X.pow 2)
    have h2 : DegreeLE (3 * X * C u : K⟮X⟯) 1 := by
      simpa using ((DegreeLE.natCast 3).mul DegreeLE.X).mul (DegreeLE.C u)
    exact (h1.sub (h2.mono (by norm_num))).add
      (((DegreeLE.C u).pow 2).mono (by norm_num))
  have ha : DegreeLE (2 * C a * C u *
      (3 * X ^ 2 - 3 * X * C u + C u ^ 2) : K⟮X⟯) 2 := by
    simpa [mul_assoc] using (DegreeLE.natCast 2).mul ((hquad.const_mul u).const_mul a)
  apply DegreeLE.sub
  · apply DegreeLE.neg
    simpa using (hc.div_X_pow 3).div_X_sub_C_pow u 2
  · simpa using (ha.div_X_pow 3).div_X_sub_C_pow u 3

/-- Multiplication by a natural-number constant preserves a degree bound. -/
theorem DegreeLE.nat_mul {f : K⟮X⟯} {m : ℤ} (hf : DegreeLE f m) (n : ℕ) :
    DegreeLE ((n : K⟮X⟯) * f) m := by
  simpa using (DegreeLE.natCast n).mul hf

/-- The cubic residual has negative degree when the leading coefficients agree. -/
theorem degreeLE_equation_residual (b e d t w : K) (r s : K⟮X⟯)
    (hr : DegreeLE r (-1)) (hs : DegreeLE s (-2))
    (ha : DegreeLE (r - C t / X - C w / X ^ 2) (-3))
    (hb : DegreeLE (s + C t / X ^ 2 + 2 * C w / X ^ 3) (-4)) :
    DegreeLE
      ((4 * X ^ 3 + C b * X ^ 2 + 2 * C e * X + C d) * (1 + s) ^ 2 -
        4 * (X + r) ^ 3 - C b * (X + r) ^ 2 -
        (2 * C e - 20 * C t) * (X + r) - (C d - 4 * C b * C t - 28 * C w)) (-1) := by
  let F : K⟮X⟯ := 4 * X ^ 3 + C b * X ^ 2 + 2 * C e * X + C d
  let A := r - C t / X - C w / X ^ 2
  let B := s + C t / X ^ 2 + 2 * C w / X ^ 3
  have hF : DegreeLE F 3 := by
    apply DegreeLE.add
    · apply DegreeLE.add
      · exact ((DegreeLE.X.pow 3).nat_mul 4).add
          (((DegreeLE.X.pow 2).const_mul b).mono (by norm_num))
      · simpa only [mul_assoc, Nat.cast_ofNat] using
          (((DegreeLE.X.const_mul e).nat_mul 2).mono (by norm_num))
    · exact (DegreeLE.C d).mono (by norm_num)
  have heq :
      F * (1 + s) ^ 2 - 4 * (X + r) ^ 3 - C b * (X + r) ^ 2 -
          (2 * C e - 20 * C t) * (X + r) - (C d - 4 * C b * C t - 28 * C w) =
        2 * F * B - 12 * X ^ 2 * A - 2 * C b * X * A -
          C (6 * b * w) / X - C (4 * e * t) / X -
          C (8 * e * w + 2 * d * t) / X ^ 2 - C (4 * d * w) / X ^ 3 +
          F * s ^ 2 - 12 * X * r ^ 2 - 4 * r ^ 3 -
          C b * r ^ 2 - C (2 * e) * r + C (20 * t) * r := by
    dsimp [F, A, B]
    simp only [map_add, map_mul, map_ofNat]
    have hx := X_ne_zero (K := K)
    field_simp
    ring
  change DegreeLE (F * _ ^ 2 - _ - _ - _ - _) _
  rw [heq]
  have h1 : DegreeLE (2 * F * B) (-1) := by simpa using (hF.nat_mul 2).mul hb
  have h2 : DegreeLE (12 * X ^ 2 * A) (-1) := by
    simpa using ((DegreeLE.X.pow 2).nat_mul 12).mul ha
  have h3 : DegreeLE (2 * C b * X * A) (-1) := by
    simpa only [mul_assoc, Nat.cast_ofNat] using
      ((((DegreeLE.X.const_mul b).nat_mul 2).mul ha).mono (by norm_num))
  have h4 : DegreeLE (C (6 * b * w) / X) (-1) := by
    simpa using (DegreeLE.C (6 * b * w)).div_X_pow 1
  have h5 : DegreeLE (C (4 * e * t) / X) (-1) := by
    simpa using (DegreeLE.C (4 * e * t)).div_X_pow 1
  have h6 : DegreeLE (C (8 * e * w + 2 * d * t) / X ^ 2) (-1) :=
    ((DegreeLE.C _).div_X_pow 2).mono (by norm_num)
  have h7 : DegreeLE (C (4 * d * w) / X ^ 3) (-1) :=
    ((DegreeLE.C _).div_X_pow 3).mono (by norm_num)
  have h8 : DegreeLE (F * s ^ 2) (-1) := by simpa using hF.mul (hs.pow 2)
  have h9 : DegreeLE (12 * X * r ^ 2) (-1) := by
    simpa using (DegreeLE.X.nat_mul 12).mul (hr.pow 2)
  have h10 : DegreeLE (4 * r ^ 3) (-1) :=
    ((hr.pow 3).nat_mul 4).mono (by norm_num)
  have h11 : DegreeLE (C b * r ^ 2) (-1) :=
    ((hr.pow 2).const_mul b).mono (by norm_num)
  have hfirst := (((((h1.sub h2).sub h3).sub h4).sub h5).sub h6).sub h7
  exact (((((hfirst.add h8).sub h9).sub h10).sub h11).sub
    (hr.const_mul (2 * e))).add (hr.const_mul (20 * t))

/-- The leading coefficients of finite pole sums give a negative-degree residual. -/
theorem degreeLE_sum_equation_residual (S : Finset K) (b e d : K) :
    let a := fun u : K => 4 * u ^ 3 + b * u ^ 2 + 2 * e * u + d
    let c := fun u : K => 6 * u ^ 2 + b * u + e
    let r := ∑ u ∈ S, polePart (C (a u)) (C (c u)) (C u) X
    let s := ∑ u ∈ S, poleSlope (C (a u)) (C (c u)) (C u) X
    let t := ∑ u ∈ S, c u
    let w := ∑ u ∈ S, (c u * u + a u)
    DegreeLE
      ((4 * X ^ 3 + C b * X ^ 2 + 2 * C e * X + C d) * (1 + s) ^ 2 -
        4 * (X + r) ^ 3 - C b * (X + r) ^ 2 -
        (2 * C e - 20 * C t) * (X + r) - (C d - 4 * C b * C t - 28 * C w)) (-1) := by
  dsimp only
  apply degreeLE_equation_residual
  · apply DegreeLE.sum
    intro u _
    exact degreeLE_polePart _ _ _
  · apply DegreeLE.sum
    intro u _
    exact degreeLE_poleSlope _ _ _
  · have h := DegreeLE.sum S
        (fun u => polePart (C (4 * u ^ 3 + b * u ^ 2 + 2 * e * u + d))
          (C (6 * u ^ 2 + b * u + e)) (C u) X -
          C (6 * u ^ 2 + b * u + e) / X -
          (C (6 * u ^ 2 + b * u + e) * C u +
            C (4 * u ^ 3 + b * u ^ 2 + 2 * e * u + d)) / X ^ 2) (-3)
        (fun u _ => degreeLE_polePart_remainder _ _ _)
    simpa only [map_sum, map_add, map_mul, Finset.sum_sub_distrib,
      ← Finset.sum_div] using h
  · have h := DegreeLE.sum S
        (fun u => poleSlope (C (4 * u ^ 3 + b * u ^ 2 + 2 * e * u + d))
          (C (6 * u ^ 2 + b * u + e)) (C u) X +
          C (6 * u ^ 2 + b * u + e) / X ^ 2 +
          2 * (C (6 * u ^ 2 + b * u + e) * C u +
            C (4 * u ^ 3 + b * u ^ 2 + 2 * e * u + d)) / X ^ 3) (-4)
        (fun u _ => degreeLE_poleSlope_remainder _ _ _)
    simpa only [map_sum, map_add, map_mul, Finset.sum_add_distrib,
      ← Finset.sum_div, ← Finset.mul_sum] using h

end RatFunc

namespace WeierstrassCurve.Velu
open RatFunc
variable {K : Type*} [Field K] [DecidableEq K]

/-- The rational Vélu coordinate satisfies the cubic identity with the explicit constant. -/
theorem rational_equation [CharZero K] (E : WeierstrassCurve K)
    (G : AddSubgroup E.toAffine.Point) [Fintype G]
    (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q) :
    let t := ∑ u ∈ kernelAbscissae E G, (6 * u ^ 2 + E.b₂ * u + E.b₄)
    let w := ∑ u ∈ kernelAbscissae E G,
      ((6 * u ^ 2 + E.b₂ * u + E.b₄) * u +
        (4 * u ^ 3 + E.b₂ * u ^ 2 + 2 * E.b₄ * u + E.b₆))
    (4 * X ^ 3 + C E.b₂ * X ^ 2 + 2 * C E.b₄ * X + C E.b₆) *
        slopeFunction E G ^ 2 =
      4 * xFunction E G ^ 3 + C E.b₂ * xFunction E G ^ 2 +
        (2 * C E.b₄ - 20 * C t) * xFunction E G +
        C E.b₆ - 4 * C E.b₂ * C t - 28 * C w := by
  let t := ∑ u ∈ kernelAbscissae E G, (6 * u ^ 2 + E.b₂ * u + E.b₄)
  let w := ∑ u ∈ kernelAbscissae E G,
    ((6 * u ^ 2 + E.b₂ * u + E.b₄) * u +
      (4 * u ^ 3 + E.b₂ * u ^ 2 + 2 * E.b₄ * u + E.b₆))
  obtain ⟨k, hk⟩ := rational_equation_up_to_constant E G hodd
  have hb := degreeLE_sum_equation_residual (kernelAbscissae E G) E.b₂ E.b₄ E.b₆
  change DegreeLE
    ((4 * X ^ 3 + C E.b₂ * X ^ 2 + 2 * C E.b₄ * X + C E.b₆) *
        slopeFunction E G ^ 2 -
      4 * xFunction E G ^ 3 - C E.b₂ * xFunction E G ^ 2 -
      (2 * C E.b₄ - 20 * C t) * xFunction E G -
      (C E.b₆ - 4 * C E.b₂ * C t - 28 * C w)) (-1) at hb
  rw [hk] at hb
  have hc : DegreeLE (C (k - (E.b₆ - 4 * E.b₂ * t - 28 * w))) (-1) := by
    convert hb using 1
    simp only [map_sub, map_mul, map_ofNat]
    ring
  have hkc := DegreeLE.const_eq_zero hc
  have hkval : k = E.b₆ - 4 * E.b₂ * t - 28 * w := sub_eq_zero.mp hkc
  rw [hkval] at hk
  simp only [map_sub, map_mul, map_ofNat] at hk
  dsimp only
  linear_combination hk

/-- A sum over nonzero kernel points is a finite sum with the identity removed. -/
theorem sum_nonzero_eq_erase (E : WeierstrassCurve K)
    (G : AddSubgroup E.toAffine.Point) [Fintype G] (f : G → K) :
    (∑ Q : Nonzero E G, f Q.val) = ∑ Q ∈ Finset.univ.erase (0 : G), f Q := by
  classical
  symm
  apply Finset.sum_subtype
  intro Q
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]
  exact ⟨fun h hz => h (Subtype.ext hz), fun h hz => h (congrArg Subtype.val hz)⟩

/-- The t coefficient is the sum over distinct kernel abscissae. -/
theorem t_eq_sum_abscissae [NeZero (2 : K)] (E : WeierstrassCurve K)
    (G : AddSubgroup E.toAffine.Point) [Fintype G]
    (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q) :
    t E G = ∑ u ∈ kernelAbscissae E G, (6 * u ^ 2 + E.b₂ * u + E.b₄) := by
  classical
  rw [t, sum_nonzero_eq_erase E G (fun Q => tTerm E (xCoord Q.val))]
  simpa only [tTerm, kernelAbscissae] using
    sum_xCoord_half E G (Finset.univ.erase 0) (by simp)
      (by intro Q hQ; simpa using hQ)
      (by intro Q hQ; exact hodd Q (Finset.mem_erase.mp hQ).1)
      (fun u => 6 * u ^ 2 + E.b₂ * u + E.b₄)

/-- The w coefficient is the second coefficient in the expansion at infinity. -/
theorem w_eq_sum_abscissae [NeZero (2 : K)] (E : WeierstrassCurve K)
    (G : AddSubgroup E.toAffine.Point) [Fintype G]
    (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q) :
    w E G = ∑ u ∈ kernelAbscissae E G,
      ((6 * u ^ 2 + E.b₂ * u + E.b₄) * u +
        (4 * u ^ 3 + E.b₂ * u ^ 2 + 2 * E.b₄ * u + E.b₆)) := by
  classical
  rw [w, sum_nonzero_eq_erase E G (fun Q => wTerm E (xCoord Q.val))]
  have h := sum_xCoord_half E G (Finset.univ.erase 0) (by simp)
    (by intro Q hQ; simpa using hQ)
    (by intro Q hQ; exact hodd Q (Finset.mem_erase.mp hQ).1)
    (fun u => 10 * u ^ 3 + 2 * E.b₂ * u ^ 2 + 3 * E.b₄ * u + E.b₆)
  change (∑ Q ∈ Finset.univ.erase (0 : G), _) = _ at h
  rw [show (∑ Q ∈ Finset.univ.erase (0 : G), wTerm E (xCoord Q.val)) =
      ∑ u ∈ kernelAbscissae E G, (10 * u ^ 3 + 2 * E.b₂ * u ^ 2 + 3 * E.b₄ * u + E.b₆)
    from h]
  apply Finset.sum_congr rfl
  intro u _
  ring

/-- The rational Vélu sums satisfy the cubic identity with the candidate coefficients. -/
theorem rational_equation_coefficients [CharZero K] (E : WeierstrassCurve K)
    (G : AddSubgroup E.toAffine.Point) [Fintype G]
    (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q) :
    (4 * X ^ 3 + C E.b₂ * X ^ 2 + 2 * C E.b₄ * X + C E.b₆) *
        slopeFunction E G ^ 2 =
      4 * xFunction E G ^ 3 + C E.b₂ * xFunction E G ^ 2 +
        (2 * C E.b₄ - 20 * C (t E G)) * xFunction E G +
        C E.b₆ - 4 * C E.b₂ * C (t E G) - 28 * C (w E G) := by
  rw [t_eq_sum_abscissae E G hodd, w_eq_sum_abscissae E G hodd]
  exact rational_equation E G hodd

end WeierstrassCurve.Velu
