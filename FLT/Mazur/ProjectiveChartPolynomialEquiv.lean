/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveSpaceCharts

/-!
# Polynomial coordinates on a projective chart

Dehomogenization sets the zeroth homogeneous coordinate to one. Its inverse
sends each polynomial variable to the corresponding homogeneous coordinate
ratio in the existing standard chart ring.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization

universe u

set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.ProjectiveSpace

variable (R : Type u) [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Constants as elements of the degree-zero homogeneous coordinate ring. -/
def constantsToZero (ι : Type*) : R →+* grading R ι 0 :=
  { toFun := fun r ↦ ⟨C r, isHomogeneous_C ι r⟩
    map_one' := Subtype.ext (map_one C)
    map_mul' := fun r s ↦ Subtype.ext (map_mul C r s)
    map_zero' := Subtype.ext (map_zero C)
    map_add' := fun r s ↦ Subtype.ext (map_add C r s) }

/-- The scalar map into a homogeneous chart ring. -/
def chartScalars (ι : Type*) (i : ι) : R →+* chartRing R ι i :=
  (fromZeroRingHom (grading R ι) _).comp (constantsToZero R ι)

instance chartAlgebra (ι : Type*) (i : ι) : Algebra R (chartRing R ι i) :=
  (chartScalars R ι i).toAlgebra

lemma val_chartScalars (ι : Type*) (i : ι) (r : R) :
    (chartScalars R ι i r).val =
      algebraMap (MvPolynomial ι R) (Localization.Away (X i)) (C r) := by
  change Localization.mk (C r) 1 = _
  exact Localization.mk_one_eq_algebraMap _

variable (n : ℕ)

/-- Substitute one for `X₀` and retain the remaining variables. -/
def dehomogenize : MvPolynomial (Fin (n + 1)) R →+* MvPolynomial (Fin n) R :=
  eval₂Hom C (Fin.cases 1 X)

@[simp]
lemma dehomogenize_zero : dehomogenize R n (X 0) = 1 := by
  simp [dehomogenize]

@[simp]
lemma dehomogenize_succ (i : Fin n) : dehomogenize R n (X i.succ) = X i := by
  simp [dehomogenize]

@[simp]
lemma dehomogenize_C (r : R) : dehomogenize R n (C r) = C r := by
  simp [dehomogenize]

/-- Evaluation at one extends across localization at the zeroth coordinate. -/
def chartToPolynomial : chartRing R (Fin (n + 1)) 0 →+* MvPolynomial (Fin n) R :=
  (Localization.awayLift (dehomogenize R n) (X 0)
    (by simp)).comp (algebraMap _ (Localization.Away (X (R := R) (0 : Fin (n + 1)))))

lemma chartToPolynomial_mk (d : ℕ) (p : MvPolynomial (Fin (n + 1)) R)
    (hp : p ∈ grading R (Fin (n + 1)) (d • 1)) :
    chartToPolynomial R n (Away.mk _ (isHomogeneous_X R 0) d p hp) =
      dehomogenize R n p := by
  change Localization.awayLift (dehomogenize R n) (X 0) (by simp)
    (Localization.mk p _) = _
  simpa using Localization.awayLift_mk (dehomogenize R n) (X 0) p 1 (by simp) d

@[simp]
lemma chartToPolynomial_coordinate (i : Fin n) :
    chartToPolynomial R n (coordinate R (Fin (n + 1)) 0 i.succ) = X i := by
  rw [coordinate, chartToPolynomial_mk, dehomogenize_succ]

@[simp]
lemma chartToPolynomial_scalar (r : R) :
    chartToPolynomial R n (chartScalars R (Fin (n + 1)) 0 r) = C r := by
  change chartToPolynomial R n (Away.mk _ (isHomogeneous_X R 0) 0 (C r) _) = _
  rw [chartToPolynomial_mk, dehomogenize_C]

/-- Substitute the existing projective coordinate ratios for affine variables. -/
def polynomialToChart : MvPolynomial (Fin n) R →ₐ[R] chartRing R (Fin (n + 1)) 0 :=
  aeval (fun i ↦ coordinate R (Fin (n + 1)) 0 i.succ)

@[simp]
lemma polynomialToChart_X (i : Fin n) :
    polynomialToChart R n (X i) = coordinate R (Fin (n + 1)) 0 i.succ := by
  simp [polynomialToChart]

lemma polynomialToChart_C (r : R) :
    polynomialToChart R n (C r) = chartScalars R (Fin (n + 1)) 0 r := by
  exact (polynomialToChart R n).commutes r

lemma chartToPolynomial_polynomialToChart (p : MvPolynomial (Fin n) R) :
    chartToPolynomial R n (polynomialToChart R n p) = p := by
  have h : (chartToPolynomial R n).comp (polynomialToChart R n).toRingHom =
      RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change chartToPolynomial R n (polynomialToChart R n (C r)) = C r
      rw [polynomialToChart_C, chartToPolynomial_scalar]
    · intro i
      change chartToPolynomial R n (polynomialToChart R n (X i)) = X i
      rw [polynomialToChart_X, chartToPolynomial_coordinate]
  exact DFunLike.congr_fun h p

/-- Scaling all inputs of a homogeneous polynomial scales its value by its degree. -/
lemma homogeneous_eval₂_scale {ι S : Type*} [CommRing S]
    (f : R →+* S) (g : ι → S) (t : S) {p : MvPolynomial ι R} {d : ℕ}
    (hp : p.IsHomogeneous d) :
    eval₂ f (fun i ↦ t * g i) p = t ^ d * eval₂ f g p := by
  classical
  conv_lhs => rw [← p.support_sum_monomial_coeff]
  conv_rhs => rw [← p.support_sum_monomial_coeff]
  simp only [eval₂_sum, eval₂_monomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [hp.degree_eq_sum_deg_support ha]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  ring

/-- The inverse of the zeroth variable in the ordinary localization. -/
def chartDenominatorInv : Localization.Away (X (R := R) (0 : Fin (n + 1))) :=
  Localization.mk 1 ⟨X 0, Submonoid.mem_powers _⟩

lemma val_coordinate_eq (i : Fin (n + 1)) :
    (coordinate R (Fin (n + 1)) 0 i).val = chartDenominatorInv R n *
      algebraMap (MvPolynomial (Fin (n + 1)) R)
        (Localization.Away (X (R := R) (0 : Fin (n + 1)))) (X i) := by
  simp only [coordinate, Away.val_mk, pow_one, chartDenominatorInv,
    ← Localization.mk_one_eq_algebraMap, Localization.mk_mul, one_mul, mul_one]

lemma val_polynomialToChart_dehomogenize (p : MvPolynomial (Fin (n + 1)) R) :
    (polynomialToChart R n (dehomogenize R n p)).val =
      eval₂ ((algebraMap (MvPolynomial (Fin (n + 1)) R)
        (Localization.Away (X (R := R) (0 : Fin (n + 1))))).comp C)
        (fun i ↦ (coordinate R (Fin (n + 1)) 0 i).val) p := by
  let v := algebraMap (chartRing R (Fin (n + 1)) 0)
    (Localization.Away (X (R := R) (0 : Fin (n + 1))))
  have h : v.comp ((polynomialToChart R n).toRingHom.comp (dehomogenize R n)) =
      eval₂Hom ((algebraMap (MvPolynomial (Fin (n + 1)) R) (Localization.Away
        (X (R := R) (0 : Fin (n + 1))))).comp C)
        (fun i ↦ (coordinate R (Fin (n + 1)) 0 i).val) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change (polynomialToChart R n (dehomogenize R n (C r))).val = _
      rw [dehomogenize_C, polynomialToChart_C]
      simpa only [eval₂Hom_C, RingHom.comp_apply] using
        val_chartScalars R (Fin (n + 1)) 0 r
    · intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simp [v]
      · simp [v]
  exact DFunLike.congr_fun h p

lemma polynomialToChart_chartToPolynomial (x : chartRing R (Fin (n + 1)) 0) :
    polynomialToChart R n (chartToPolynomial R n x) = x := by
  obtain ⟨d, p, hp, rfl⟩ := Away.mk_surjective (grading R (Fin (n + 1)))
    (isHomogeneous_X R 0) x
  rw [chartToPolynomial_mk]
  apply val_injective
  rw [val_polynomialToChart_dehomogenize]
  simp_rw [val_coordinate_eq]
  rw [homogeneous_eval₂_scale R _ _ _ (by simpa using hp)]
  have heval : eval₂ ((algebraMap (MvPolynomial (Fin (n + 1)) R) (Localization.Away
      (X (R := R) (0 : Fin (n + 1))))).comp C)
      (fun i ↦ algebraMap (MvPolynomial (Fin (n + 1)) R)
        (Localization.Away (X (R := R) (0 : Fin (n + 1))))
        (X i)) p = algebraMap (MvPolynomial (Fin (n + 1)) R) (Localization.Away
          (X (R := R) (0 : Fin (n + 1)))) p := by
    rw [← hom_eval₂, eval₂_eta]
  rw [heval]
  simp only [chartDenominatorInv, Localization.mk_pow, one_pow,
    ← Localization.mk_one_eq_algebraMap, Localization.mk_mul, one_mul,
    mul_one, Away.val_mk]
  rfl

/-- Polynomial coordinates identify affine space with the zeroth projective chart. -/
def chartPolynomialEquiv :
    MvPolynomial (Fin n) R ≃ₐ[R] chartRing R (Fin (n + 1)) 0 :=
  { polynomialToChart R n with
    invFun := chartToPolynomial R n
    left_inv := chartToPolynomial_polynomialToChart R n
    right_inv := polynomialToChart_chartToPolynomial R n }

@[simp]
lemma chartPolynomialEquiv_X (i : Fin n) :
    chartPolynomialEquiv R n (X i) = coordinate R (Fin (n + 1)) 0 i.succ :=
  polynomialToChart_X R n i

end FLT.Mazur.ProjectiveSpace
