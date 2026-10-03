/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexPadicScalars

/-! # The scalar embedding has the standard p-adic residue -/

@[expose] public noncomputable section
open scoped NNReal
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- Natural approximations determine integral p-adic maps into a separated ring. -/
theorem padicInt_hom_ext_adic {R : Type*} [CommRing R]
    [IsHausdorff (Ideal.span {(p : R)}) R] (f g : ℤ_[p] →+* R) : f = g := by
  apply RingHom.ext
  intro x
  apply (IsHausdorff.eq_iff_smodEq (I := Ideal.span {(p : R)})).mpr
  intro n
  rw [SModEq.sub_mem]
  simp only [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp (PadicInt.appr_spec n x)
  have hf : f x - (x.appr n : R) = (p : R) ^ n * f y := by
    simpa only [map_sub, map_natCast, map_mul, map_pow] using congrArg f hy
  have hg : g x - (x.appr n : R) = (p : R) ^ n * g y := by
    simpa only [map_sub, map_natCast, map_mul, map_pow] using congrArg g hy
  exact ⟨f y - g y, by rw [mul_sub, ← hf, ← hg]; ring⟩

/-- The standard inclusion of Z_p takes values in the actual integer ring of C_p. -/
def complexPadicIntToInteger : ℤ_[p] →+* 𝓞_ℂ_[p] where
  toFun x := ⟨algebraMap ℚ_[p] ℂ_[p] x, by
    change Valued.v (algebraMap ℚ_[p] ℂ_[p] x) ≤ (1 : ℝ≥0)
    rw [← NNReal.coe_le_coe, complex_valuation_coe]
    simpa using x.property⟩
  map_zero' := Subtype.ext (by simp)
  map_one' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)

/-- Integral theta agrees with the standard scalar inclusion. -/
theorem complexPadicIntToAinf_theta (x : ℤ_[p]) :
    complexTheta p (complexPadicIntToAinf p x) = complexPadicIntToInteger p x :=
  RingHom.congr_fun (padicInt_hom_ext_adic p
    ((complexTheta p).comp (complexPadicIntToAinf p)) (complexPadicIntToInteger p)) x

/-- Completed theta sends an integral scalar to its usual value in C_p. -/
@[simp] theorem complexPadicIntToDeRham_theta (x : ℤ_[p]) :
    complexDeRhamTheta p (complexPadicIntToDeRham p x) = algebraMap ℚ_[p] ℂ_[p] x := by
  change complexDeRhamTheta p
    (algebraMap (ComplexAinfInvertP p) (ComplexBDeRhamPlus p)
      (algebraMap (Ainf p) (ComplexAinfInvertP p) (complexPadicIntToAinf p x))) = _
  rw [complexDeRhamTheta_algebraMap, complexPadicIntToAinf_theta]
  rfl

/-- Completed theta is compatible with the standard Q_p scalar embedding. -/
@[simp] theorem complexPadicToDeRham_theta (x : ℚ_[p]) :
    complexDeRhamTheta p (complexPadicToDeRham p x) = algebraMap ℚ_[p] ℂ_[p] x := by
  have h : (complexDeRhamTheta p).comp (complexPadicToDeRham p) =
      algebraMap ℚ_[p] ℂ_[p] := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p])
    ext y
    simp only [RingHom.comp_apply, complexPadicToDeRham_int, complexPadicIntToDeRham_theta]
    rfl
  exact RingHom.congr_fun h x

/-- A nonzero scalar never belongs to the first theta-filtration step. -/
theorem complexPadicToDeRham_notMem (x : ℚ_[p]) (hx : x ≠ 0) :
    complexPadicToDeRham p x ∉ Ideal.span {complexDeRhamParameter p} := by
  rw [← complexDeRhamTheta_ker, RingHom.mem_ker, complexPadicToDeRham_theta]
  exact (map_ne_zero_iff _ (algebraMap ℚ_[p] ℂ_[p]).injective).mpr hx

/-- In particular p-power decay cannot be inferred in the theta-adic filtration. -/
theorem complexDeRham_prime_pow_notMem (n : ℕ) :
    (p : ComplexBDeRhamPlus p) ^ n ∉ Ideal.span {complexDeRhamParameter p} := by
  have h := complexPadicToDeRham_notMem p ((p : ℚ_[p]) ^ n)
    (pow_ne_zero n (by exact_mod_cast (Fact.out : p.Prime).ne_zero))
  simpa only [map_pow, map_natCast] using h

end PadicHodgeTheory
