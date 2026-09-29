/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalizationDegreePiece

/-!
# Degree shifts by chart variables

Every coordinate occurring in the denominator product is a unit. Its integer
powers shift the concrete degree pieces, including negative degrees.
-/

@[expose] public noncomputable section

open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory Opposite

namespace FLT.Mazur.ProjectiveSpace.LocalizationDegree

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (ι : Type u)
variable {q : ℕ} (a : Fin (q + 1) → ι)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The complementary product after removing one position, retaining repetitions. -/
def complement (j : Fin (q + 1)) : MvPolynomial ι R :=
  TwistCech.coordinateProduct R ι (a ∘ j.succAbove)

lemma product_eq (j : Fin (q + 1)) :
    TwistCech.coordinateProduct R ι a = X (a j) * complement R ι a j := by
  exact Fin.prod_univ_succAbove (fun k ↦ X (a k)) j

lemma complement_homogeneous (j : Fin (q + 1)) :
    complement R ι a j ∈ grading R ι q :=
  TwistCech.coordinateProduct_homogeneous R ι (a ∘ j.succAbove)

/-- Each chart variable divides the localized product and therefore becomes invertible. -/
lemma variable_isUnit (j : Fin (q + 1)) :
    IsUnit (algebraMap (MvPolynomial ι R) (Full R ι a) (X (a j))) :=
  IsLocalization.Away.isUnit_of_dvd (TwistCech.coordinateProduct R ι a)
    ⟨complement R ι a j, product_eq R ι a j⟩

/-- The actual chart-variable unit in the full polynomial localization. -/
def variableUnit (j : Fin (q + 1)) : (Full R ι a)ˣ := (variable_isUnit R ι a j).unit

@[simp] lemma variableUnit_val (j : Fin (q + 1)) :
    (variableUnit R ι a j : Full R ι a) =
      algebraMap (MvPolynomial ι R) (Full R ι a) (X (a j)) :=
  (variable_isUnit R ι a j).unit_spec

lemma variableUnit_inv (j : Fin (q + 1)) :
    (↑((variableUnit R ι a j)⁻¹) : Full R ι a) = fraction R ι a (complement R ι a j) 1 := by
  apply (Units.mul_right_inj (variableUnit R ι a j)).mp
  rw [Units.mul_inv, variableUnit_val]
  rw [← Localization.mk_one_eq_algebraMap, fraction, Localization.mk_mul]
  simpa only [pow_one, OneMemClass.coe_one, one_mul, ← product_eq] using
    (Localization.mk_self ⟨TwistCech.coordinateProduct R ι a,
      Submonoid.mem_powers _⟩).symm

lemma variable_mem (j : Fin (q + 1)) :
    (variableUnit R ι a j : Full R ι a) ∈ piece R ι a 1 := by
  refine ⟨0, 1, X (a j), isHomogeneous_X R (a j), by simp, ?_⟩
  rw [variableUnit_val]
  unfold fraction
  convert Localization.mk_one_eq_algebraMap (M := Submonoid.powers
    (TwistCech.coordinateProduct R ι a)) (X (a j)) using 2
  exact Subtype.ext (pow_zero _)

lemma variable_inv_mem (j : Fin (q + 1)) :
    (↑((variableUnit R ι a j)⁻¹) : Full R ι a) ∈ piece R ι a (-1) := by
  exact ⟨1, q, complement R ι a j, complement_homogeneous R ι a j,
    by push_cast; ring, (variableUnit_inv R ι a j).symm⟩

lemma one_mem_piece : (1 : Full R ι a) ∈ piece R ι a 0 := by
  refine ⟨0, 0, 1, isHomogeneous_one ι R, by simp, ?_⟩
  simp [fraction]

lemma pow_mem_piece {n : ℤ} {x : Full R ι a} (hx : x ∈ piece R ι a n) (k : ℕ) :
    x ^ k ∈ piece R ι a (k * n) := by
  induction k with
  | zero => simpa using one_mem_piece R ι a
  | succ k ih =>
    simpa [pow_succ, Nat.cast_add, add_mul] using mul_mem_piece R ι a ih hx

/-- Integer powers have their expected degree, with no sign restriction. -/
lemma variable_zpow_mem (j : Fin (q + 1)) (n : ℤ) :
    (↑(variableUnit R ι a j ^ n) : Full R ι a) ∈ piece R ι a n := by
  cases n with
  | ofNat k => simpa using pow_mem_piece R ι a (variable_mem R ι a j) k
  | negSucc k =>
    rw [zpow_negSucc, ← inv_pow]
    convert pow_mem_piece R ι a (variable_inv_mem R ι a j) (k + 1) using 1
    simp [Int.negSucc_eq]

/-- Multiplication by `Xⱼⁿ` identifies degree zero with degree `n`. -/
def shift (j : Fin (q + 1)) (n : ℤ) : piece R ι a 0 ≃ₗ[R] piece R ι a n where
  toFun x := ⟨(↑(variableUnit R ι a j ^ n) : Full R ι a) * x,
    by simpa using mul_mem_piece R ι a (variable_zpow_mem R ι a j n) x.property⟩
  invFun x := ⟨(↑(variableUnit R ι a j ^ (-n)) : Full R ι a) * x,
    by simpa using mul_mem_piece R ι a (variable_zpow_mem R ι a j (-n)) x.property⟩
  left_inv x := by
    apply Subtype.ext
    change (↑(variableUnit R ι a j ^ (-n)) : Full R ι a) *
      ((↑(variableUnit R ι a j ^ n) : Full R ι a) * x.val) = x.val
    rw [← mul_assoc, ← Units.val_mul, ← zpow_add]
    simp
  right_inv x := by
    apply Subtype.ext
    change (↑(variableUnit R ι a j ^ n) : Full R ι a) *
      ((↑(variableUnit R ι a j ^ (-n)) : Full R ι a) * x.val) = x.val
    rw [← mul_assoc, ← Units.val_mul, ← zpow_add]
    simp
  map_add' x y := Subtype.ext (mul_add _ _ _)
  map_smul' r x := Subtype.ext (mul_smul_comm _ _ _)

@[simp] lemma shift_val (j : Fin (q + 1)) (n : ℤ) (x : piece R ι a 0) :
    (shift R ι a j n x : Full R ι a) = (↑(variableUnit R ι a j ^ n) : Full R ι a) * x :=
  rfl

/-- Changing from the `k` basis to the `j` basis multiplies by `(Xₖ/Xⱼ)ⁿ`. -/
lemma shift_change (j k : Fin (q + 1)) (n : ℤ) (x : piece R ι a 0) :
    ((shift R ι a j n).symm (shift R ι a k n x) : Full R ι a) =
      (↑((variableUnit R ι a k / variableUnit R ι a j) ^ n) : Full R ι a) * x := by
  change (↑(variableUnit R ι a j ^ (-n)) : Full R ι a) *
    ((↑(variableUnit R ι a k ^ n) : Full R ι a) * x.val) = _
  rw [← mul_assoc, ← Units.val_mul]
  congr 2
  simp [div_eq_mul_inv, mul_zpow, zpow_neg, mul_comm]

open FLT.Mazur.FCurve.ModuleSheafUnitCocycle

/-- Restriction from one chart to the tuple's homogeneous coordinate ring. -/
def chartMap (j : Fin (q + 1)) : chartRing R ι (a j) →+* TwistCech.intersectionRing R ι a :=
  awayMap (grading R ι) (complement_homogeneous R ι a j) (product_eq R ι a j)

/-- The chart ratio as an actual homogeneous fraction on the tuple intersection. -/
def coefficient (j k : Fin (q + 1)) : TwistCech.intersectionRing R ι a :=
  chartMap R ι a j (coordinate R ι (a j) (a k))

lemma coefficient_val (j k : Fin (q + 1)) :
    (coefficient R ι a j k).val =
      (variableUnit R ι a k : Full R ι a) * ↑((variableUnit R ι a j)⁻¹) := by
  simp only [coefficient, chartMap, coordinate, awayMap_mk, Away.val_mk, pow_one]
  rw [variableUnit_inv, variableUnit_val, ← Localization.mk_one_eq_algebraMap]
  simp only [fraction, Localization.mk_mul, pow_one, one_mul]

/-- The ratio `Xₖ/Xⱼ` is a unit already in the homogeneous degree-zero ring. -/
def coefficientUnit (j k : Fin (q + 1)) : (TwistCech.intersectionRing R ι a)ˣ where
  val := coefficient R ι a j k
  inv := coefficient R ι a k j
  val_inv := by
    apply HomogeneousLocalization.val_injective
    simp only [val_mul, val_one, coefficient_val]
    simp only [← Units.val_mul, mul_assoc, inv_mul_cancel_left, mul_inv_cancel, Units.val_one]
  inv_val := by
    apply HomogeneousLocalization.val_injective
    simp only [val_mul, val_one, coefficient_val]
    simp only [← Units.val_mul, mul_assoc, inv_mul_cancel_left, mul_inv_cancel, Units.val_one]

lemma coefficientUnit_map (j k : Fin (q + 1)) :
    Units.map (algebraMap (TwistCech.intersectionRing R ι a) (Full R ι a)).toMonoidHom
      (coefficientUnit R ι a j k) = variableUnit R ι a k / variableUnit R ι a j := by
  apply Units.ext
  exact (coefficient_val R ι a j k).trans (by simp [div_eq_mul_inv])

/-- The coefficient for any integer twist agrees in the full localization. -/
lemma coefficientUnit_zpow_val (j k : Fin (q + 1)) (n : ℤ) :
    ((coefficientUnit R ι a j k ^ n : (TwistCech.intersectionRing R ι a)ˣ).val).val =
      (↑((variableUnit R ι a k / variableUnit R ι a j) ^ n) : Full R ι a) := by
  change (Units.map
    (algebraMap (TwistCech.intersectionRing R ι a) (Full R ι a)).toMonoidHom
      (coefficientUnit R ι a j k ^ n)).val = _
  rw [map_zpow, coefficientUnit_map]

lemma chartMap_sections (j : Fin (q + 1)) (r : chartRing R ι (a j)) :
    TwistCech.intersectionRingEquiv R ι q a (chartMap R ι a j r) =
      res (TwistCech.intersection_le R ι q a j)
        ((Proj.awayToSection (grading R ι) (X (a j))).hom r) := by
  have h := congrArg (fun f ↦ f.hom r)
    (Proj.awayMap_awayToSection (grading R ι) (complement_homogeneous R ι a j)
      (product_eq R ι a j))
  change (Proj.awayToSection (grading R ι) (TwistCech.coordinateProduct R ι a)).hom
    (chartMap R ι a j r) = res _
      ((Proj.awayToSection (grading R ι) (X (a j))).hom r) at h
  rw [TwistCech.intersectionRingEquiv_apply, h]
  simp only [res_res]
  rfl

lemma coefficient_sections (j k : Fin (q + 1)) :
    TwistCech.intersectionRingEquiv R ι q a (coefficient R ι a j k) =
      (restrictUnits R ι (le_inf (TwistCech.intersection_le R ι q a j)
        (TwistCech.intersection_le R ι q a k))
          (twistTransition R ι 1 (a j) (a k))).val := by
  rw [coefficient, chartMap_sections]
  have h := congrArg (fun f ↦ f.hom (coordinate R ι (a j) (a k)))
    (Proj.awayMap_awayToSection (grading R ι) (isHomogeneous_X R (a k))
      (f := X (a j)) rfl)
  change (Proj.awayToSection (grading R ι) (X (a j) * X (a k))).hom
    (toOverlap R ι (a j) (a k) (coordinate R ι (a j) (a k))) =
      res _ ((Proj.awayToSection (grading R ι) (X (a j))).hom
        (coordinate R ι (a j) (a k))) at h
  change _ = res _ (res _ ((Proj.awayToSection (grading R ι) (X (a j) * X (a k))).hom
    (transitionUnit R ι 1 (a j) (a k))))
  rw [transitionUnit_one, ratioUnit_val, h]
  simp only [res_res]
  rfl

/-- Under the Proj section comparison the basis change is the actual twist transition. -/
lemma coefficientUnit_sections (j k : Fin (q + 1)) (n : ℤ) :
    Units.map (TwistCech.intersectionRingEquiv R ι q a).toMonoidHom
      (coefficientUnit R ι a j k ^ n) =
        restrictUnits R ι (le_inf (TwistCech.intersection_le R ι q a j)
          (TwistCech.intersection_le R ι q a k))
            (twistTransition R ι n (a j) (a k)) := by
  have h : Units.map (TwistCech.intersectionRingEquiv R ι q a).toMonoidHom
      (coefficientUnit R ι a j k) =
        restrictUnits R ι (le_inf (TwistCech.intersection_le R ι q a j)
          (TwistCech.intersection_le R ι q a k))
            (twistTransition R ι 1 (a j) (a k)) :=
    Units.ext (coefficient_sections R ι a j k)
  rw [map_zpow, h]
  simp only [twistTransition, transitionSection, transitionUnit, zpow_one, map_zpow]

/-- The chart change coefficient in the shift equivalence is the geometric transition. -/
lemma shift_change_coefficient (j k : Fin (q + 1)) (n : ℤ) (x : piece R ι a 0) :
    ((shift R ι a j n).symm (shift R ι a k n x) : Full R ι a) =
      ((coefficientUnit R ι a j k ^ n : (TwistCech.intersectionRing R ι a)ˣ).val).val * x := by
  rw [shift_change, coefficientUnit_zpow_val]

end FLT.Mazur.ProjectiveSpace.LocalizationDegree
