/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluIdentity
/-!
# Vélu coordinates satisfy the candidate curve equation

Evaluation is a ring homomorphism on rational functions regular at the chosen
point. Applying it to the rational Vélu identity proves that xMap and yMap
satisfy the candidate equation away from the kernel, in characteristic zero,
for a finite kernel without nonzero two-torsion.

The equation is unconditional under these hypotheses. Landing in the nonsingular
point group additionally requires a nonzero target discriminant; that geometric
obligation and additivity remain separate.
-/

@[expose] public section

open scoped Polynomial BigOperators

namespace RatFunc
variable {K : Type*} [Field K]

/-- A rational function is regular at a point when its reduced denominator does not vanish. -/
def RegularAt (x : K) (f : K⟮X⟯) : Prop := f.denom.eval x ≠ 0

/-- A nonvanishing denominator multiple certifies regularity. -/
theorem RegularAt.of_dvd (x : K) {f : K⟮X⟯} {q : K[X]}
    (h : f.denom ∣ q) (hq : q.eval x ≠ 0) : RegularAt x f := by
  intro hz
  exact hq (Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero h hz)

/-- Constants are regular at every point. -/
theorem RegularAt.C (x c : K) : RegularAt x (RatFunc.C c) := by
  simp [RegularAt]

/-- The indeterminate is regular at every point. -/
theorem RegularAt.X (x : K) : RegularAt x (RatFunc.X : K⟮X⟯) := by
  simp [RegularAt]

/-- Regular rational functions are closed under addition. -/
theorem RegularAt.add {x : K} {f g : K⟮X⟯} (hf : RegularAt x f) (hg : RegularAt x g) :
    RegularAt x (f + g) := by
  apply RegularAt.of_dvd x (denom_add_dvd f g)
  simpa only [Polynomial.eval_mul] using mul_ne_zero hf hg

/-- Regular rational functions are closed under multiplication. -/
theorem RegularAt.mul {x : K} {f g : K⟮X⟯} (hf : RegularAt x f) (hg : RegularAt x g) :
    RegularAt x (f * g) := by
  apply RegularAt.of_dvd x (denom_mul_dvd f g)
  simpa only [Polynomial.eval_mul] using mul_ne_zero hf hg

/-- Regular rational functions are closed under negation. -/
theorem RegularAt.neg {x : K} {f : K⟮X⟯} (hf : RegularAt x f) :
    RegularAt x (-f) := by
  simpa only [map_neg, map_one, neg_one_mul] using (RegularAt.C x (-1)).mul hf

/-- The subring of rational functions regular at a given point. -/
def regularSubring (x : K) : Subring K⟮X⟯ where
  carrier := RegularAt x
  zero_mem' := by
    change RegularAt x (0 : K⟮X⟯)
    simpa only [map_zero] using RegularAt.C x 0
  one_mem' := by
    change RegularAt x (1 : K⟮X⟯)
    simpa only [map_one] using RegularAt.C x 1
  add_mem' := RegularAt.add
  mul_mem' := RegularAt.mul
  neg_mem' := RegularAt.neg

/-- Evaluation as a ring homomorphism on regular rational functions. -/
noncomputable def evalAt (x : K) : regularSubring x →+* K where
  toFun f := RatFunc.eval (RingHom.id K) x f.val
  map_zero' := by simp
  map_one' := by simp
  map_add' f g := by
    exact eval_add (RingHom.id K) x
      (by simpa only [Polynomial.eval₂_id] using (show f.val.denom.eval x ≠ 0 from f.property))
      (by simpa only [Polynomial.eval₂_id] using (show g.val.denom.eval x ≠ 0 from g.property))
  map_mul' f g := by
    exact eval_mul (RingHom.id K) x
      (by simpa only [Polynomial.eval₂_id] using (show f.val.denom.eval x ≠ 0 from f.property))
      (by simpa only [Polynomial.eval₂_id] using (show g.val.denom.eval x ≠ 0 from g.property))

/-- A polynomial fraction is regular where its presented denominator is nonzero. -/
theorem regularAt_div_polynomial (x : K) (p q : K[X]) (hq : q.eval x ≠ 0) :
    RegularAt x (algebraMap K[X] K⟮X⟯ p / algebraMap K[X] K⟮X⟯ q) :=
  RegularAt.of_dvd x (denom_div_dvd p q) hq

/-- Evaluation of a polynomial fraction with nonvanishing denominator. -/
theorem eval_div_polynomial (x : K) (p q : K[X]) (hq : q.eval x ≠ 0) :
    eval (RingHom.id K) x
        (algebraMap K[X] K⟮X⟯ p / algebraMap K[X] K⟮X⟯ q) =
      p.eval x / q.eval x := by
  let f := algebraMap K[X] K⟮X⟯ p / algebraMap K[X] K⟮X⟯ q
  have hq0 : q ≠ 0 := fun h => hq (by simp [h])
  have hf := regularAt_div_polynomial x p q hq
  have hc : f.num * q = p * f.denom := (num_mul_eq_mul_denom_iff hq0).mpr rfl
  have h := congrArg (Polynomial.eval x) hc
  simp only [Polynomial.eval_mul] at h
  change f.num.eval₂ (RingHom.id K) x / f.denom.eval₂ (RingHom.id K) x = _
  simp only [Polynomial.eval₂_id]
  exact (div_eq_div_iff hf hq).mpr h

open WeierstrassCurve.Velu

/-- A pole contribution is regular and evaluates as expected off its pole. -/
theorem regular_eval_polePart (a c u x : K) (hx : x ≠ u) :
    RegularAt x (polePart (C a) (C c) (C u) X) ∧
      eval (RingHom.id K) x (polePart (C a) (C c) (C u) X) = polePart a c u x := by
  let p : K[X] := Polynomial.C c * (Polynomial.X - Polynomial.C u) + Polynomial.C a
  let q : K[X] := (Polynomial.X - Polynomial.C u) ^ 2
  have hq : q.eval x ≠ 0 := by simpa [q] using pow_ne_zero 2 (sub_ne_zero.mpr hx)
  have hr : polePart (C a) (C c) (C u) X =
      algebraMap K[X] K⟮X⟯ p / algebraMap K[X] K⟮X⟯ q := by
    simp only [p, q, map_add, map_mul, map_sub, map_pow, algebraMap_C, algebraMap_X, polePart]
    have hu := X_sub_C_ne_zero u
    field_simp
  constructor
  · rw [hr]
    exact regularAt_div_polynomial x p q hq
  · rw [hr, eval_div_polynomial x p q hq]
    simp only [p, q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, polePart]
    field_simp

/-- A slope contribution is regular and evaluates as expected off its pole. -/
theorem regular_eval_poleSlope (a c u x : K) (hx : x ≠ u) :
    RegularAt x (poleSlope (C a) (C c) (C u) X) ∧
      eval (RingHom.id K) x (poleSlope (C a) (C c) (C u) X) = poleSlope a c u x := by
  let p : K[X] := -Polynomial.C c * (Polynomial.X - Polynomial.C u) - 2 * Polynomial.C a
  let q : K[X] := (Polynomial.X - Polynomial.C u) ^ 3
  have hq : q.eval x ≠ 0 := by simpa [q] using pow_ne_zero 3 (sub_ne_zero.mpr hx)
  have hr : poleSlope (C a) (C c) (C u) X =
      algebraMap K[X] K⟮X⟯ p / algebraMap K[X] K⟮X⟯ q := by
    simp only [p, q, map_mul, map_sub, map_neg, map_pow, map_ofNat,
      algebraMap_C, algebraMap_X, poleSlope]
    have hu := X_sub_C_ne_zero u
    field_simp
  constructor
  · rw [hr]
    exact regularAt_div_polynomial x p q hq
  · rw [hr, eval_div_polynomial x p q hq]
    simp only [p, q, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_neg, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_ofNat, poleSlope]
    field_simp

/-- Evaluation preserves sums of regular rational functions. -/
theorem RegularAt.eval_add {x : K} {f g : K⟮X⟯}
    (hf : RegularAt x f) (hg : RegularAt x g) :
    eval (RingHom.id K) x (f + g) =
      eval (RingHom.id K) x f + eval (RingHom.id K) x g :=
  RatFunc.eval_add (RingHom.id K) x
    (by simpa only [RegularAt, Polynomial.eval₂_id] using hf)
    (by simpa only [RegularAt, Polynomial.eval₂_id] using hg)

/-- Regularity and evaluation commute with finite sums. -/
theorem regular_eval_sum {ι : Type*} (S : Finset ι) (f : ι → K⟮X⟯) (g : ι → K) (x : K)
    (h : ∀ u ∈ S, RegularAt x (f u) ∧ eval (RingHom.id K) x (f u) = g u) :
    RegularAt x (∑ u ∈ S, f u) ∧
      eval (RingHom.id K) x (∑ u ∈ S, f u) = ∑ u ∈ S, g u := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [RegularAt]
  | @insert u S hu ih =>
    have hU := h u (Finset.mem_insert_self u S)
    have hS := ih (fun v hv => h v (Finset.mem_insert_of_mem hv))
    rw [Finset.sum_insert hu, Finset.sum_insert hu]
    exact ⟨hU.1.add hS.1, by rw [hU.1.eval_add hS.1, hU.2, hS.2]⟩

end RatFunc

namespace WeierstrassCurve.Velu
open RatFunc
variable {K : Type*} [Field K] [DecidableEq K]

/-- The rational x-coordinate evaluates to the sum over kernel abscissae. -/
theorem regular_eval_xFunction (E : WeierstrassCurve K)
    (G : AddSubgroup E.toAffine.Point) [Fintype G] (x : K)
    (hx : x ∉ kernelAbscissae E G) :
    RegularAt x (xFunction E G) ∧
      eval (RingHom.id K) x (xFunction E G) =
        x + ∑ u ∈ kernelAbscissae E G,
          polePart (4 * u ^ 3 + E.b₂ * u ^ 2 + 2 * E.b₄ * u + E.b₆)
            (6 * u ^ 2 + E.b₂ * u + E.b₄) u x := by
  have hsum := regular_eval_sum (kernelAbscissae E G) _ _ x
    (fun u hu => regular_eval_polePart
      (4 * u ^ 3 + E.b₂ * u ^ 2 + 2 * E.b₄ * u + E.b₆)
      (6 * u ^ 2 + E.b₂ * u + E.b₄) u x
      (fun h => hx (h ▸ hu)))
  unfold xFunction
  exact ⟨(RegularAt.X x).add hsum.1,
    by rw [(RegularAt.X x).eval_add hsum.1, eval_X, hsum.2]⟩

/-- The rational derivative evaluates to the slope sum over kernel abscissae. -/
theorem regular_eval_slopeFunction (E : WeierstrassCurve K)
    (G : AddSubgroup E.toAffine.Point) [Fintype G] (x : K)
    (hx : x ∉ kernelAbscissae E G) :
    RegularAt x (slopeFunction E G) ∧
      eval (RingHom.id K) x (slopeFunction E G) =
        1 + ∑ u ∈ kernelAbscissae E G,
          poleSlope (4 * u ^ 3 + E.b₂ * u ^ 2 + 2 * E.b₄ * u + E.b₆)
            (6 * u ^ 2 + E.b₂ * u + E.b₄) u x := by
  have hsum := regular_eval_sum (kernelAbscissae E G) _ _ x
    (fun u hu => regular_eval_poleSlope
      (4 * u ^ 3 + E.b₂ * u ^ 2 + 2 * E.b₄ * u + E.b₆)
      (6 * u ^ 2 + E.b₂ * u + E.b₄) u x
      (fun h => hx (h ▸ hu)))
  have h1 : RegularAt x (1 : K⟮X⟯) := by
    simpa only [map_one] using RegularAt.C x 1
  unfold slopeFunction
  exact ⟨h1.add hsum.1, by rw [h1.eval_add hsum.1, eval_one, hsum.2]⟩

/-- Evaluation of the rational cubic identity away from the kernel abscissae. -/
theorem evaluated_rational_equation [CharZero K] (E : WeierstrassCurve K)
    (G : AddSubgroup E.toAffine.Point) [Fintype G]
    (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q) (x : K) (hx : x ∉ kernelAbscissae E G) :
    (4 * x ^ 3 + E.b₂ * x ^ 2 + 2 * E.b₄ * x + E.b₆) *
        eval (RingHom.id K) x (slopeFunction E G) ^ 2 =
      4 * eval (RingHom.id K) x (xFunction E G) ^ 3 +
        E.b₂ * eval (RingHom.id K) x (xFunction E G) ^ 2 +
        (2 * E.b₄ - 20 * t E G) * eval (RingHom.id K) x (xFunction E G) +
        E.b₆ - 4 * E.b₂ * t E G - 28 * w E G := by
  let c (a : K) : regularSubring x := ⟨C a, RegularAt.C x a⟩
  let z : regularSubring x := ⟨X, RegularAt.X x⟩
  let Y : regularSubring x := ⟨xFunction E G, (regular_eval_xFunction E G x hx).1⟩
  let D : regularSubring x := ⟨slopeFunction E G, (regular_eval_slopeFunction E G x hx).1⟩
  have h : (4 * z ^ 3 + c E.b₂ * z ^ 2 + 2 * c E.b₄ * z + c E.b₆) * D ^ 2 =
      4 * Y ^ 3 + c E.b₂ * Y ^ 2 + (2 * c E.b₄ - 20 * c (t E G)) * Y +
        c E.b₆ - 4 * c E.b₂ * c (t E G) - 28 * c (w E G) := by
    apply Subtype.ext
    exact rational_equation_coefficients E G hodd
  have hc (a : K) : evalAt x (c a) = a := by
    change eval (RingHom.id K) x (C a) = a
    simp
  have hz : evalAt x z = x := by
    change eval (RingHom.id K) x X = x
    exact eval_X _ _
  have he := congrArg (evalAt x) h
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, hc, hz] at he
  exact he

/-- Pairing nonzero inverse points turns a half-weighted sum into an abscissa sum. -/
theorem sum_kernel_half [NeZero (2 : K)] (E : WeierstrassCurve K)
    (G : AddSubgroup E.toAffine.Point) [Fintype G]
    (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q) (f : K → K) (a : K) :
    (∑ Q : G, if Q = 0 then a else f (xCoord Q.val) / 2) =
      a + ∑ u ∈ kernelAbscissae E G, f u := by
  classical
  let d (Q : G) := if Q = 0 then a else f (xCoord Q.val) / 2
  have h := Finset.sum_erase_add Finset.univ d (Finset.mem_univ (0 : G))
  change (∑ Q : G, d Q) = _
  rw [← h, show d 0 = a by simp [d], add_comm]
  congr 1
  calc
    (∑ Q ∈ Finset.univ.erase (0 : G), d Q) =
        ∑ Q ∈ Finset.univ.erase (0 : G), f (xCoord Q.val) / 2 := by
      apply Finset.sum_congr rfl
      intro Q hQ
      exact ite_eq_right (Finset.mem_erase.mp hQ).1
    _ = ∑ u ∈ kernelAbscissae E G, f u :=
      sum_xCoord_half E G (Finset.univ.erase 0) (by simp)
        (by intro Q hQ; simpa using hQ)
        (by intro Q hQ; exact hodd Q (Finset.mem_erase.mp hQ).1) f

/-- The affine x-map equals the sum over distinct kernel abscissae. -/
theorem xMap_eq_sum_abscissae [NeZero (2 : K)] (E : WeierstrassCurve K)
    (G : AddSubgroup E.toAffine.Point) [Fintype G]
    (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q) {x y : K}
    (hP : E.toAffine.Nonsingular x y) (hPG : Affine.Point.some x y hP ∉ G) :
    xMap E G (.some x y hP) =
      x + ∑ u ∈ kernelAbscissae E G,
        polePart (4 * u ^ 3 + E.b₂ * u ^ 2 + 2 * E.b₄ * u + E.b₆)
          (6 * u ^ 2 + E.b₂ * u + E.b₄) u x := by
  classical
  rw [xMap_eq_sum_rational E G hP hPG, ← sum_kernel_half E G hodd]
  apply Finset.sum_congr rfl
  intro Q _
  split_ifs
  · rfl
  · dsimp [tTerm, polePart]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

/-- The affine slope factor equals the sum over distinct kernel abscissae. -/
theorem slopeFactor_eq_sum_abscissae [NeZero (2 : K)] (E : WeierstrassCurve K)
    (G : AddSubgroup E.toAffine.Point) [Fintype G]
    (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q) (x : K) :
    slopeFactor E G x =
      1 + ∑ u ∈ kernelAbscissae E G,
        poleSlope (4 * u ^ 3 + E.b₂ * u ^ 2 + 2 * E.b₄ * u + E.b₆)
          (6 * u ^ 2 + E.b₂ * u + E.b₄) u x := by
  classical
  rw [slopeFactor, ← sum_kernel_half E G hodd]
  apply Finset.sum_congr rfl
  intro Q _
  split_ifs
  · rfl
  · dsimp [tTerm, poleSlope]
    field_simp

/-- An affine point outside the kernel has x-coordinate outside its abscissae. -/
theorem x_not_mem_kernelAbscissae (E : WeierstrassCurve K)
    (G : AddSubgroup E.toAffine.Point) [Fintype G] {x y : K}
    (hP : E.toAffine.Nonsingular x y) (hPG : Affine.Point.some x y hP ∉ G) :
    x ∉ kernelAbscissae E G := by
  classical
  intro hx
  obtain ⟨Q, hQ, hqx⟩ := Finset.mem_image.mp hx
  have hQ0 : Q.val ≠ 0 := fun h => (Finset.mem_erase.mp hQ).1 (Subtype.ext h)
  rcases hval : Q.val with _ | ⟨u, v, hu⟩
  · exact hQ0 hval
  · have hxu : u = x := by simpa only [hval, xCoord] using hqx
    exact xCoord_ne_of_not_mem E G hP hPG hu (hval ▸ Q.property) hxu.symm

/-- The Vélu coordinate sums satisfy the candidate affine curve equation off the kernel. -/
theorem equation_xMap_yMap [CharZero K] (E : WeierstrassCurve K)
    (G : AddSubgroup E.toAffine.Point) [Fintype G]
    (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q) {x y : K}
    (hP : E.toAffine.Nonsingular x y) (hPG : Affine.Point.some x y hP ∉ G) :
    (curve E G).toAffine.Equation
      (xMap E G (.some x y hP)) (yMap E G (.some x y hP)) := by
  apply (equation_iff_univariate_identity E G hP hPG).2
  have hx := x_not_mem_kernelAbscissae E G hP hPG
  have h := evaluated_rational_equation E G hodd x hx
  rw [(regular_eval_xFunction E G x hx).2, (regular_eval_slopeFunction E G x hx).2,
    ← xMap_eq_sum_abscissae E G hodd hP hPG, ← slopeFactor_eq_sum_abscissae E G hodd x] at h
  exact h

/-- The affine equation holds for every source point outside the kernel. -/
theorem equation_xMap_yMap_of_not_mem [CharZero K] (E : WeierstrassCurve K)
    (G : AddSubgroup E.toAffine.Point) [Fintype G]
    (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q) (P : E.toAffine.Point) (hP : P ∉ G) :
    (curve E G).toAffine.Equation (xMap E G P) (yMap E G P) := by
  cases P with
  | zero => exact (hP G.zero_mem).elim
  | some x y hxy => exact equation_xMap_yMap E G hodd hxy hP

/-- Once the candidate discriminant is nonzero, the coordinate sums land in its point group. -/
theorem nonsingular_xMap_yMap [CharZero K] (E : WeierstrassCurve K)
    (G : AddSubgroup E.toAffine.Point) [Fintype G]
    (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q) (hΔ : (curve E G).Δ ≠ 0)
    (P : E.toAffine.Point) (hP : P ∉ G) :
    (curve E G).toAffine.Nonsingular (xMap E G P) (yMap E G P) :=
  (Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp
    (equation_xMap_yMap_of_not_mem E G hodd P hP)

end WeierstrassCurve.Velu
