/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluEvaluation
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Ellipticity of the Vélu curve

A repeated root of the target cubic would force a rational function with a pole
at infinity to satisfy a differential square identity. At any zero of its reduced
numerator, that identity contradicts the simple roots of the source cubic.
Thus the explicit Vélu target has nonzero discriminant over an algebraically
closed field of characteristic zero. Additivity is a separate obligation.
-/

@[expose] public section

open scoped Polynomial
namespace Polynomial
variable {K : Type*} [Field K] [CharZero K]

/-- A differential square identity with a source having only simple roots
excludes numerator roots. -/
theorem no_root_of_differential_square
    (p q F R : K[X]) (hp : p ≠ 0) (hcop : IsCoprime p q)
    (hF : F ≠ 0) (hsep : ∀ a : K, F.rootMultiplicity a ≤ 1)
    (heq : F * (p.derivative * q - p * q.derivative)^2 = p^2 * R)
    (a : K) : ¬p.IsRoot a := by
  intro ha
  have hm : 0 < p.rootMultiplicity a := (rootMultiplicity_pos hp).mpr ha
  have hqa : ¬q.IsRoot a := by
    intro hq
    obtain ⟨u, v, huv⟩ := hcop
    have hh := congrArg (eval a) huv
    simp [ha.eq_zero, hq.eq_zero] at hh
  have hq : q ≠ 0 := by
    intro hz
    exact hqa (by simp [hz])
  have hdp : p.derivative ≠ 0 := by
    intro hz
    rw [eq_C_of_derivative_eq_zero hz] at ha
    have hc : p.coeff 0 ≠ 0 := by
      intro hc
      apply hp
      rw [eq_C_of_derivative_eq_zero hz, hc, C_0]
    exact not_isRoot_C _ _ hc ha
  let W := p.derivative * q - p * q.derivative
  have hn : ¬(X - C a) ^ p.rootMultiplicity a ∣ W := by
    intro hd
    have hd' : (X - C a) ^ p.rootMultiplicity a ∣ p.derivative * q := by
      have hd2 := dvd_mul_of_dvd_left (p.pow_rootMultiplicity_dvd a) q.derivative
      simpa [W] using dvd_add hd hd2
    have hl := (le_rootMultiplicity_iff (mul_ne_zero hdp hq)).mpr hd'
    rw [rootMultiplicity_mul (mul_ne_zero hdp hq),
      derivative_rootMultiplicity_of_root ha, rootMultiplicity_eq_zero hqa] at hl
    omega
  have hW : W ≠ 0 := by
    intro hz
    exact hn (hz ▸ dvd_zero _)
  have hWm : W.rootMultiplicity a < p.rootMultiplicity a := by
    exact lt_of_not_ge (fun h => hn ((le_rootMultiplicity_iff hW).mp h))
  have hmul : F * W^2 ≠ 0 := mul_ne_zero hF (pow_ne_zero _ hW)
  have hdiv : p^2 ∣ F * W^2 := ⟨R, heq⟩
  have hle := rootMultiplicity_le_rootMultiplicity_of_dvd hmul hdiv a
  rw [rootMultiplicity_mul hmul] at hle
  simp only [pow_two, rootMultiplicity_mul (mul_ne_zero hp hp),
    rootMultiplicity_mul (mul_ne_zero hW hW)] at hle
  have := hsep a
  omega
end Polynomial

namespace RatFunc
variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- A rational function with a pole at infinity cannot satisfy this differential square identity. -/
theorem not_differential_square
    (f : K⟮X⟯) (hf : ¬ DegreeLE f 0)
    (F : K[X]) (hF : F ≠ 0) (hsep : ∀ a : K, F.rootMultiplicity a ≤ 1)
    (k c : K) :
    algebraMap K[X] K⟮X⟯ F * (formalDerivation f)^2 ≠
      f^2 * (C k * f + C c) := by
  intro heq
  have hf0 : f ≠ 0 := fun h => hf (Or.inl h)
  have hn : f.num.natDegree ≠ 0 := by
    intro h
    apply hf
    right
    simp [intDegree, h]
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root f.num (by
    intro h
    exact hn (Polynomial.natDegree_eq_of_degree_eq_some h))
  have hq := algebraMap_ne_zero (K := K) f.denom_ne_zero
  have hpoly :
      F * (f.num.derivative * f.denom - f.num * f.denom.derivative)^2 =
        f.num^2 * ((Polynomial.C k * f.num + Polynomial.C c * f.denom) * f.denom) := by
    apply algebraMap_injective K
    simp only [map_mul, map_sub, map_add, map_pow, algebraMap_C]
    rw [formalDerivation_apply, formalDeriv] at heq
    conv at heq => rhs; rw [← f.num_div_denom]
    simp only [map_sub, map_mul] at heq
    field_simp [hq] at heq
    convert heq using 1; ring
  exact Polynomial.no_root_of_differential_square f.num f.denom F _
    (num_ne_zero hf0) f.isCoprime_num_denom hF hsep hpoly a ha
end RatFunc

namespace WeierstrassCurve.Velu
open RatFunc
variable {K : Type*} [Field K] [DecidableEq K]

/-- Every constant shift of the Vélu x-coordinate still has a pole at infinity. -/
theorem xFunction_sub_C_not_degreeLE (E : WeierstrassCurve K)
    (G : AddSubgroup E.toAffine.Point) [Fintype G] (a : K) :
    ¬ DegreeLE (xFunction E G - C a) 0 := by
  intro h
  have hs := DegreeLE.sum (kernelAbscissae E G)
    (fun u => polePart (C (4 * u^3 + E.b₂*u^2 + 2*E.b₄*u + E.b₆))
      (C (6*u^2 + E.b₂*u + E.b₄)) (C u) X) (-1)
    (fun u _ => degreeLE_polePart _ _ _)
  have hx : DegreeLE (X : K⟮X⟯) 0 := by
    convert (h.add (DegreeLE.C a)).sub (hs.mono (by omega)) using 1
    simp [xFunction]
  rcases hx with hx | hx
  · exact RatFunc.X_ne_zero hx
  · simp at hx

end WeierstrassCurve.Velu

namespace RatFunc
open Polynomial
variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- A cubic related by the normalized differential equation has no repeated roots. -/
theorem cubic_discr_ne_zero_of_differential_equation
    (Y : K⟮X⟯) (hY : ∀ a : K, ¬DegreeLE (Y - RatFunc.C a) 0)
    (F : K[X]) (hF : F ≠ 0) (hsep : ∀ a : K, F.rootMultiplicity a ≤ 1)
    (T : Cubic K) (hT : T.a ≠ 0)
    (heq : algebraMap K[X] K⟮X⟯ F * (formalDerivation Y)^2 =
      Polynomial.eval₂ RatFunc.C Y T.toPoly) : T.discr ≠ 0 := by
  have hs : (T.toPoly.map (RingHom.id K)).Splits := IsAlgClosed.splits _
  obtain ⟨a, b, c, hr⟩ :=
    (Cubic.splits_iff_roots_eq_three (φ := RingHom.id K) hT).mp hs
  have ht : T.toPoly =
      Polynomial.C T.a * (Polynomial.X - Polynomial.C a) *
        (Polynomial.X - Polynomial.C b) * (Polynomial.X - Polynomial.C c) :=
    Cubic.eq_prod_three_roots (φ := RingHom.id K) hT hr
  rw [ht] at heq
  simp only [eval₂_mul, eval₂_sub, eval₂_C, eval₂_X] at heq
  have hn (u v : K)
      (h : algebraMap K[X] K⟮X⟯ F * (formalDerivation Y)^2 =
        RatFunc.C T.a * (Y - RatFunc.C u)^2 * (Y - RatFunc.C v)) : False := by
    apply not_differential_square (Y - RatFunc.C u) (hY u) F hF hsep
      T.a (T.a * (u - v))
    simp only [map_sub, formalDerivation_C, sub_zero]
    rw [h]
    simp only [map_mul, map_sub]
    ring
  apply (Cubic.discr_ne_zero_iff_roots_ne (φ := RingHom.id K) hT hr).mpr
  refine ⟨?_, ?_, ?_⟩
  · intro hab
    subst b
    apply hn a c
    linear_combination heq
  · intro hac
    subst c
    apply hn a b
    linear_combination heq
  · intro hbc
    subst c
    apply hn b a
    linear_combination heq
end RatFunc

namespace WeierstrassCurve.Velu
open RatFunc
variable {K : Type*} [Field K] [DecidableEq K] [CharZero K] [IsAlgClosed K]

omit [DecidableEq K] in
/-- The two-torsion cubic of an elliptic curve has only simple roots. -/
theorem twoTorsion_rootMultiplicity_le_one (E : WeierstrassCurve K) [E.IsElliptic]
    (a : K) : E.twoTorsionPolynomial.toPoly.rootMultiplicity a ≤ 1 := by
  classical
  have hd := E.twoTorsionPolynomial_discr_ne_zero (isUnit_iff_ne_zero.mpr (by norm_num))
    E.isUnit_Δ
  have hn := (Cubic.discr_ne_zero_iff_roots_nodup (φ := RingHom.id K)
    (P := E.twoTorsionPolynomial) (by norm_num [twoTorsionPolynomial])
    (IsAlgClosed.splits _)).mp hd
  change E.twoTorsionPolynomial.toPoly.roots.Nodup at hn
  simpa only [Polynomial.count_roots] using
    Multiset.nodup_iff_count_le_one.mp hn a

/-- The explicit Vélu target of an odd kernel has nonzero discriminant. -/
theorem curve_discr_ne_zero (E : WeierstrassCurve K) [E.IsElliptic]
    (G : AddSubgroup E.toAffine.Point) [Fintype G]
    (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q) : (curve E G).Δ ≠ 0 := by
  have heq : algebraMap K[X] K⟮X⟯ E.twoTorsionPolynomial.toPoly *
      (formalDerivation (xFunction E G))^2 =
      Polynomial.eval₂ C (xFunction E G) (curve E G).twoTorsionPolynomial.toPoly := by
    rw [derivation_xFunction]
    convert rational_equation_coefficients E G hodd using 1
    · simp only [twoTorsionPolynomial, Cubic.toPoly, map_add, map_mul, map_pow,
        map_ofNat, algebraMap_C, algebraMap_X]
    · simp only [twoTorsionPolynomial, Cubic.toPoly, Polynomial.eval₂_add,
        Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C,
        Polynomial.eval₂_X]
      simp only [curve, b₂, b₄, b₆, map_sub, map_add, map_mul, map_pow, map_ofNat]
      ring
  have hd := cubic_discr_ne_zero_of_differential_equation (xFunction E G)
    (xFunction_sub_C_not_degreeLE E G) E.twoTorsionPolynomial.toPoly
    (Cubic.ne_zero_of_a_ne_zero (by norm_num [twoTorsionPolynomial]))
    (twoTorsion_rootMultiplicity_le_one E)
    (curve E G).twoTorsionPolynomial (by norm_num [twoTorsionPolynomial]) heq
  rw [twoTorsionPolynomial_discr] at hd
  exact (mul_ne_zero_iff.mp hd).2
end WeierstrassCurve.Velu

namespace WeierstrassCurve.Velu
variable {K : Type*} [Field K] [DecidableEq K] [CharZero K] [IsAlgClosed K]

/-- The target of the odd-kernel Vélu construction is an elliptic curve. -/
theorem curve_isElliptic (E : WeierstrassCurve K) [E.IsElliptic]
    (G : AddSubgroup E.toAffine.Point) [Fintype G]
    (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q) : (curve E G).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (curve_discr_ne_zero E G hodd)⟩

/-- The actual coordinate sums land in the nonsingular locus away from the kernel. -/
theorem nonsingular_xMap_yMap_of_not_mem (E : WeierstrassCurve K) [E.IsElliptic]
    (G : AddSubgroup E.toAffine.Point) [Fintype G]
    (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)
    (P : E.toAffine.Point) (hP : P ∉ G) :
    (curve E G).toAffine.Nonsingular (xMap E G P) (yMap E G P) := by
  let := curve_isElliptic E G hodd
  exact Affine.equation_iff_nonsingular.mp (equation_xMap_yMap_of_not_mem E G hodd P hP)
end WeierstrassCurve.Velu
