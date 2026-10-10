/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveHomogeneousEvaluation
public import FLT.Mazur.ProjectiveUnitChartPoint

/-!
# Scheme points from homogeneous unit denominators

Evaluation through two positive homogeneous denominators gives the same
actual projective scheme morphism. The comparison uses their product chart.
-/

@[expose] public noncomputable section
open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.ProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
variable (R : Type u) [CommRing R] (ι : Type u)
variable {S : Type u} [CommRing S]

/-- Evaluation commutes with restriction to a homogeneous product chart. -/
lemma homogeneousEval_awayMap (F : MvPolynomial ι R →+* S)
    (s t : MvPolynomial ι R) {m n : ℕ} (hm : s ∈ grading R ι m)
    (hn : t ∈ grading R ι n) (a b : Sˣ) (ha : F s = a) (hb : F t = b) :
    (homogeneousEval R ι F (s * t) (a * b) (by simp [ha, hb])).comp
        (awayMap (grading R ι) hn rfl) = homogeneousEval R ι F s a ha := by
  ext z
  obtain ⟨d, p, hp, rfl⟩ := Away.mk_surjective (grading R ι) hm z
  simp only [RingHom.comp_apply, awayMap_mk, homogeneousEval_mk, map_mul, map_pow, hb]
  simp only [mul_inv_rev, Units.val_mul, mul_pow]
  calc
    F p * (b : S) ^ d * ((↑b⁻¹ : S) ^ d * (↑a⁻¹ : S) ^ d) =
        F p * ((b : S) * ↑b⁻¹) ^ d * (↑a⁻¹ : S) ^ d := by rw [mul_pow]; ring
    _ = F p * (↑a⁻¹ : S) ^ d := by simp

/-- The actual affine-test-scheme morphism defined through a homogeneous chart. -/
def homogeneousPoint (F : MvPolynomial ι R →+* S) (s : MvPolynomial ι R)
    {m : ℕ} (hm : s ∈ grading R ι m) (hpos : 0 < m)
    (a : Sˣ) (ha : F s = a) : Spec (.of S) ⟶ space R ι :=
  Spec.map (CommRingCat.ofHom (homogeneousEval R ι F s a ha)) ≫
    Proj.awayι (grading R ι) s hm hpos

/-- Passing to a product denominator does not change the scheme morphism. -/
lemma homogeneousPoint_mul (F : MvPolynomial ι R →+* S)
    (s t : MvPolynomial ι R) {m n : ℕ} (hm : s ∈ grading R ι m)
    (hn : t ∈ grading R ι n) (hpos : 0 < m)
    (a b : Sˣ) (ha : F s = a) (hb : F t = b) :
    homogeneousPoint R ι F (s * t) (SetLike.mul_mem_graded hm hn)
        (hpos.trans_le (Nat.le_add_right m n)) (a * b) (by simp [ha, hb]) =
      homogeneousPoint R ι F s hm hpos a ha := by
  rw [homogeneousPoint, homogeneousPoint, ← homogeneousEval_awayMap R ι F s t hm hn a b ha hb]
  change _ = Spec.map (CommRingCat.ofHom (awayMap (grading R ι) hn rfl) ≫ _) ≫ _
  rw [Spec.map_comp, Category.assoc, Proj.SpecMap_awayMap_awayι]
  rfl

/-- The chosen positive homogeneous unit denominator does not affect the point. -/
lemma homogeneousPoint_change (F : MvPolynomial ι R →+* S)
    (s t : MvPolynomial ι R) {m n : ℕ} (hm : s ∈ grading R ι m)
    (hn : t ∈ grading R ι n) (hpos : 0 < m) (hnpos : 0 < n)
    (a b : Sˣ) (ha : F s = a) (hb : F t = b) :
    homogeneousPoint R ι F s hm hpos a ha =
      homogeneousPoint R ι F t hn hnpos b hb := by
  rw [← homogeneousPoint_mul R ι F s t hm hn hpos a b ha hb,
    ← homogeneousPoint_mul R ι F t s hn hm hnpos b a hb ha]
  congr 1 <;> first | exact mul_comm _ _ | exact Nat.add_comm _ _

/-- The construction recovers the scheme point on a standard unit-coordinate chart. -/
lemma homogeneousPoint_variable (f : R →+* S) (x : ι → S)
    (i : ι) (a : Sˣ) (hi : x i = a) :
    homogeneousPoint R ι (eval₂Hom f x) (X i) (isHomogeneous_X R i)
        (by decide) a (by simpa using hi) = unitChartPoint R ι f x i a hi := by
  rw [homogeneousPoint, homogeneousEval_variable]
  rfl

end FLT.Mazur.ProjectiveSpace
