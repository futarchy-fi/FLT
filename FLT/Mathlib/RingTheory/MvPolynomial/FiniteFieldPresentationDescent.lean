/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.MvPolynomial.OriginTensorEquiv
public import FLT.Mathlib.RingTheory.MvPolynomial.LocalizedFiniteFieldDescent
public import Mathlib.FieldTheory.IntermediateField.Algebraic

/-! # Descend a localized regular quotient by coefficient-field base change -/

@[expose] public noncomputable section

open scoped TensorProduct

namespace MvPolynomial

variable (k K : Type*) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K] (n : ℕ)

/-- Base change of a localized quotient extends only its coefficient field. -/
def originFieldQuotientEquiv (rs : List (OriginLocalization k n)) :
    K ⊗[k] (OriginLocalization k n ⧸ Ideal.ofList rs) ≃ₐ[K]
      (OriginLocalization K n ⧸ Ideal.ofList (rs.map (originLocalizationMap k K n))) :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := k) K (OriginLocalization k n) K
    (Ideal.ofList rs)).trans <|
      Ideal.quotientEquivAlg _ _ (originTensorEquiv k K n) (by
        change Ideal.ofList (rs.map (originLocalizationMap k K n)) =
          ((Ideal.ofList rs).map
            (Algebra.TensorProduct.includeRight : OriginLocalization k n →ₐ[k]
              K ⊗[k] OriginLocalization k n).toRingHom).map
                (originTensorEquiv k K n).toRingHom
        rw [Ideal.map_map, Ideal.map_ofList]
        congr 1
        apply List.map_congr_left
        intro x _
        simp [originTensorEquiv_tmul])

/-- The coefficient-field quotient equivalence preserves the original coordinate formula. -/
@[simp] theorem originFieldQuotientEquiv_tmul
    (rs : List (OriginLocalization k n)) (c : K) (x : OriginLocalization k n) :
    originFieldQuotientEquiv k K n rs (c ⊗ₜ Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (algebraMap K (OriginLocalization K n) c *
        originLocalizationMap k K n x) := by
  simp [originFieldQuotientEquiv, Ideal.quotientEquivAlg_mk]

variable {k K n} {A : Type*} [CommRing A] [Algebra K A]

/-- A regular localized presentation descends to a finite field and recovers the given
algebra by coefficient-field base change, with its original quotient coordinate map. -/
theorem exists_finite_field_regular_presentation
    (rs : List (OriginLocalization K n))
    (hreg : RingTheory.Sequence.IsRegular (OriginLocalization K n) rs)
    (e : (OriginLocalization K n ⧸ Ideal.ofList rs) ≃ₐ[K] A) :
    ∃ E : IntermediateField k K, FiniteDimensional k E ∧
      ∃ qs : List (OriginLocalization E n), qs.map (originLocalizationMap E K n) = rs ∧
        qs.length = rs.length ∧ RingTheory.Sequence.IsRegular (OriginLocalization E n) qs ∧
        ∃ e' : (K ⊗[E] (OriginLocalization E n ⧸ Ideal.ofList qs)) ≃ₐ[K] A,
          ∀ c x, e' (c ⊗ₜ Ideal.Quotient.mk _ x) =
            e (Ideal.Quotient.mk _ (algebraMap K (OriginLocalization K n) c *
              originLocalizationMap E K n x)) := by
  obtain ⟨E, hE, qs, hqs, hlen, hreg⟩ :=
    exists_finite_field_of_localized_regular_list (k := k) hreg
  let eqv := (originFieldQuotientEquiv E K n qs).trans
    ((Ideal.quotientEquivAlgOfEq K (congrArg Ideal.ofList hqs)).trans e)
  refine ⟨E, hE, qs, hqs, hlen, hreg, eqv, fun c x ↦ ?_⟩
  simp [eqv]

end MvPolynomial
