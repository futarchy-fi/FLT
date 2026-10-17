/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.LaurentReciprocalErrorConjugation
public import FLT.Mazur.LaurentSquareZeroBoundaryFactorization

/-!
# Correct a full residual relative to a reciprocal base parameter

The base parameter is retained exactly. Its reciprocal reduction determines
which complementary fields extend across the two adjacent node boundaries.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentReciprocalRelativeCorrection
open LaurentPolynomial LaurentBoundaryVectorField LaurentBoundaryCorrectionSplit
variable {R : Type*} [CommRing R] (p : R) (r : ℕ) (he : (p ^ r) ^ 2 = 0)
local notation "L" => R[T;T⁻¹]
local notation "I" => Ideal.span (Set.singleton p)
local notation "J" => Ideal.map (algebraMap R L) I
local notation "S" => LaurentSquareZeroAutomorphism.equiv (p ^ r) he

/-- The initial boundary field is the reciprocal of the nonpositive relative error. -/
def initialField (q : L) : L := reciprocalField (nonpositivePart q)

/-- The neighboring right boundary removes the positive part of the relative error. -/
def neighborField (q : L) : L := -positivePart q

/-- The initial field extends across its node origin. -/
theorem initialField_boundary (q : L) (d : ℤ) (hd : d ≤ 0) :
    (initialField q).coeff d = 0 := reciprocal_nonpositive_coeff q d hd

/-- The neighboring field also extends across its boundary origin. -/
theorem neighborField_boundary (q : L) (d : ℤ) (hd : d ≤ 0) :
    (neighborField q).coeff d = 0 := by
  rw [neighborField, AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply,
    positivePart_coeff, ite_eq_right (show ¬ (0 : ℤ) < d by omega), neg_zero]

/-- Full base conjugation agrees with reciprocal transport on the top correction layer. -/
theorem initial_conjugation (B : L ≃ₐ[R] L)
    (hB : ∀ z, B.symm z - invert z ∈ J) (hJ : J ^ (1 + r) = ⊥) (q : L) :
    (B.trans (S (initialField q))).trans B.symm = S (nonpositivePart q) := by
  apply AlgEquiv.coe_toAlgHom_injective
  change B.symm.toAlgHom.comp ((S (initialField q)).toAlgHom.comp B.toAlgHom) = _
  have hc := LaurentReciprocalErrorConjugation.conjugation_eq I r B.symm
    (S (initialField q)).toAlgHom hB
    (fun z ↦ LaurentReciprocalErrorConjugation.subst_sub_mem p r he (initialField q) z) hJ
  simp only [AlgEquiv.symm_symm] at hc
  rw [hc]
  change invert.toAlgHom.comp
    ((LaurentSquareZeroAutomorphism.subst (p ^ r) he (initialField q)).comp
      invert.toAlgHom) = _
  rw [LaurentSquareZeroAutomorphism.subst_reciprocal, initialField,
    reciprocalField_involutive]
  rfl

/-- The complete relative residual cancels while the entire original base remains. -/
theorem cancel_relative (B E : L ≃ₐ[R] L)
    (hB : ∀ z, B.symm z - invert z ∈ J) (hJ : J ^ (1 + r) = ⊥) (q : L)
    (hE : E.trans B.symm = S q) :
    ((S (neighborField q)).trans E).trans (S (initialField q)).symm = B := by
  have hsplit : (S (neighborField q)).trans (S q) = S (nonpositivePart q) := by
    apply AlgEquiv.coe_toAlgHom_injective
    change (LaurentSquareZeroAutomorphism.subst (p ^ r) he q).comp
      (LaurentSquareZeroAutomorphism.subst (p ^ r) he (neighborField q)) = _
    rw [LaurentSquareZeroAutomorphism.subst_comp]
    congr 1
    exact (sub_eq_add_neg q (positivePart q)).symm
  have hc := initial_conjugation p r he B hB hJ q
  ext z : 1
  have hh := congrArg (fun f : L ≃ₐ[R] L ↦ f (S (neighborField q) z)) hE
  have hs := congrArg (fun f : L ≃ₐ[R] L ↦ f z) hsplit
  have hb := congrArg (fun f : L ≃ₐ[R] L ↦ f z) hc
  simp only [AlgEquiv.trans_apply] at hh hs hb ⊢
  rw [← hh, ← hb] at hs
  have h := B.symm.injective hs
  rw [h, AlgEquiv.symm_apply_apply]

end FLT.Mazur.LaurentReciprocalRelativeCorrection
