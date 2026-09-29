/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveTwistCech

/-!
# Integer degree pieces of polynomial chart localizations

The degree piece consists of actual homogeneous fractions with the prescribed
numerator degree minus denominator degree. The degree zero piece recovers the
homogeneous localization, with its natural constant scalar action.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace FLT.Mazur.ProjectiveSpace.LocalizationDegree

universe u

variable (R : Type u) [CommRing R] (ι : Type u)
variable {q : ℕ} (a : Fin (q + 1) → ι)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The full localization at the tuple's coordinate product. -/
abbrev Full := Localization.Away (TwistCech.coordinateProduct R ι a)

/-- A fraction with a power of the coordinate product as denominator. -/
def fraction (f : MvPolynomial ι R) (k : ℕ) : Full R ι a :=
  Localization.mk f ⟨TwistCech.coordinateProduct R ι a ^ k, ⟨k, rfl⟩⟩

lemma fraction_add (f g : MvPolynomial ι R) (k l : ℕ) :
    fraction R ι a f k + fraction R ι a g l =
      fraction R ι a
        (f * TwistCech.coordinateProduct R ι a ^ l +
          g * TwistCech.coordinateProduct R ι a ^ k) (k + l) := by
  simp only [fraction, Localization.add_mk, pow_add]
  congr 1
  ring

lemma fraction_mul (f g : MvPolynomial ι R) (k l : ℕ) :
    fraction R ι a f k * fraction R ι a g l = fraction R ι a (f * g) (k + l) := by
  simp only [fraction, Localization.mk_mul, pow_add]
  rfl

lemma fraction_smul (r : R) (f : MvPolynomial ι R) (k : ℕ) :
    r • fraction R ι a f k = fraction R ι a (r • f) k :=
  Localization.smul_mk _ _ _

/-- The concrete homogeneous-fraction predicate, including negative degrees. -/
def HasDegree (n : ℤ) (x : Full R ι a) : Prop :=
  ∃ (k d : ℕ) (f : MvPolynomial ι R),
    f ∈ grading R ι d ∧ (d : ℤ) - k * (q + 1) = n ∧ fraction R ι a f k = x

lemma hasDegree_zero (n : ℤ) : HasDegree R ι a n 0 := by
  refine ⟨(-n).toNat, n.toNat + (-n).toNat * q, 0, zero_mem _, ?_, ?_⟩
  · push_cast
    have := Int.toNat_sub_toNat_neg n
    nlinarith
  · exact Localization.mk_zero _

lemma hasDegree_add {n : ℤ} {x y : Full R ι a}
    (hx : HasDegree R ι a n x) (hy : HasDegree R ι a n y) :
    HasDegree R ι a n (x + y) := by
  obtain ⟨k, d, f, hf, hd, rfl⟩ := hx
  obtain ⟨l, e, g, hg, he, rfl⟩ := hy
  have hdeg : e + k * (q + 1) = d + l * (q + 1) := by
    zify
    omega
  refine ⟨k + l, d + l * (q + 1), _, ?_, ?_, (fraction_add R ι a f g k l).symm⟩
  · apply (grading R ι _).add_mem
    · exact SetLike.mul_mem_graded hf
        (SetLike.pow_mem_graded l (TwistCech.coordinateProduct_homogeneous R ι a))
    · rw [← hdeg]
      exact SetLike.mul_mem_graded hg
        (SetLike.pow_mem_graded k (TwistCech.coordinateProduct_homogeneous R ι a))
  · push_cast
    nlinarith

lemma hasDegree_smul (r : R) {n : ℤ} {x : Full R ι a}
    (hx : HasDegree R ι a n x) : HasDegree R ι a n (r • x) := by
  obtain ⟨k, d, f, hf, hd, rfl⟩ := hx
  exact ⟨k, d, r • f, (grading R ι d).smul_mem r hf, hd,
    (fraction_smul R ι a r f k).symm⟩

/-- The integer degree piece as an actual submodule of the full localization. -/
def piece (n : ℤ) : Submodule R (Full R ι a) where
  carrier := {x | HasDegree R ι a n x}
  zero_mem' := hasDegree_zero R ι a n
  add_mem' := hasDegree_add R ι a
  smul_mem' := fun r _ hx ↦ hasDegree_smul R ι a r hx

/-- Membership is exactly representability by a homogeneous fraction of degree `n`. -/
lemma mem_piece_iff (n : ℤ) (x : Full R ι a) :
    x ∈ piece R ι a n ↔ ∃ (k d : ℕ) (f : MvPolynomial ι R),
      f ∈ grading R ι d ∧ (d : ℤ) - k * (q + 1) = n ∧ fraction R ι a f k = x :=
  Iff.rfl

/-- Multiplication adds the integer degrees of concrete fractions. -/
lemma mul_mem_piece {n m : ℤ} {x y : Full R ι a}
    (hx : x ∈ piece R ι a n) (hy : y ∈ piece R ι a m) :
    x * y ∈ piece R ι a (n + m) := by
  obtain ⟨k, d, f, hf, hd, rfl⟩ := hx
  obtain ⟨l, e, g, hg, he, rfl⟩ := hy
  refine ⟨k + l, d + e, f * g, SetLike.mul_mem_graded hf hg, ?_,
    (fraction_mul R ι a f g k l).symm⟩
  push_cast
  nlinarith

/-- The canonical inclusion of the usual homogeneous localization. -/
def zeroVal : TwistCech.intersectionRing R ι a →+ Full R ι a where
  toFun := HomogeneousLocalization.val
  map_zero' := HomogeneousLocalization.val_zero
  map_add' := HomogeneousLocalization.val_add

/-- Constant scalars act through the ordinary polynomial localization. -/
instance zeroModule : Module R (TwistCech.intersectionRing R ι a) :=
  Function.Injective.module R (zeroVal R ι a)
    (HomogeneousLocalization.val_injective _)
    (HomogeneousLocalization.val_smul _)

lemma zeroVal_mem (x : TwistCech.intersectionRing R ι a) :
    zeroVal R ι a x ∈ piece R ι a 0 := by
  obtain ⟨k, f, hf, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (grading R ι) (TwistCech.coordinateProduct_homogeneous R ι a) x
  refine ⟨k, k * (q + 1), f, hf, ?_, rfl⟩
  push_cast
  ring

/-- The usual degree-zero localization has exactly the concrete degree-zero fractions. -/
lemma range_zeroVal : Set.range (zeroVal R ι a) = (piece R ι a 0 : Set (Full R ι a)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact zeroVal_mem R ι a y
  · rintro ⟨k, d, f, hf, hd, rfl⟩
    have h : d = k * (q + 1) := by
      zify
      omega
    subst d
    exact ⟨HomogeneousLocalization.Away.mk (grading R ι)
      (TwistCech.coordinateProduct_homogeneous R ι a) k f hf, rfl⟩

/-- The degree-zero identification is linear for the constant `R` action. -/
def zeroEquiv : TwistCech.intersectionRing R ι a ≃ₗ[R] piece R ι a 0 :=
  LinearEquiv.ofBijective
    { toFun := fun x ↦ ⟨zeroVal R ι a x, zeroVal_mem R ι a x⟩
      map_add' := fun x y ↦ Subtype.ext (HomogeneousLocalization.val_add x y)
      map_smul' := fun r x ↦ Subtype.ext (HomogeneousLocalization.val_smul _ r x) }
    ⟨fun x y h ↦ HomogeneousLocalization.val_injective _ (congrArg Subtype.val h),
      fun x ↦ by
        obtain ⟨y, hy⟩ := (Set.ext_iff.mp (range_zeroVal R ι a) x.val).mpr x.property
        exact ⟨y, Subtype.ext hy⟩⟩

@[simp] lemma zeroEquiv_val (x : TwistCech.intersectionRing R ι a) :
    (zeroEquiv R ι a x : Full R ι a) = x.val := rfl

end FLT.Mazur.ProjectiveSpace.LocalizationDegree
