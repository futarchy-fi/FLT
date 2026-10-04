/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.MvPolynomial.LocalizedFiniteFieldDescent
public import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Reconstruct localized quotient presentations after coefficient descent -/

@[expose] public noncomputable section

open scoped TensorProduct

namespace MvPolynomial

variable (k K : Type*) [Field k] [Field K] [Algebra k K] (n : ℕ)

/-- The coefficient-extension algebra structure on the polynomial local ring. -/
abbrev originLocalizationAlgebra : Algebra (OriginLocalization k n) (OriginLocalization K n) :=
  (originLocalizationMap k K n).toAlgebra

attribute [local instance] originLocalizationAlgebra

/-- Reconstruct the quotient after extending its localized polynomial source. -/
def originQuotientBaseChangeEquiv (rs : List (OriginLocalization k n)) :
    OriginLocalization K n ⊗[OriginLocalization k n]
        (OriginLocalization k n ⧸ Ideal.ofList rs) ≃ₐ[OriginLocalization K n]
      (OriginLocalization K n ⧸ Ideal.ofList (rs.map (originLocalizationMap k K n))) :=
  (Algebra.TensorProduct.quotIdealMapEquivTensorQuot
    (OriginLocalization K n) (Ideal.ofList rs)).symm.trans
    (Ideal.quotientEquivAlgOfEq _ (Ideal.map_ofList _ rs))

/-- The quotient base-change equivalence retains every original polynomial coordinate. -/
@[simp] theorem originQuotientBaseChangeEquiv_tmul
    (rs : List (OriginLocalization k n)) (b : OriginLocalization K n)
    (a : OriginLocalization k n) :
    originQuotientBaseChangeEquiv k K n rs (b ⊗ₜ (Ideal.Quotient.mk _ a)) =
      Ideal.Quotient.mk _ (originLocalizationMap k K n a * b) := rfl

/-- The descended quotient embeds in its geometric extension; no new relations appear. -/
theorem origin_quotientMap_injective (rs : List (OriginLocalization k n)) :
    Function.Injective (Ideal.quotientMap
      ((Ideal.ofList rs).map (originLocalizationMap k K n))
      (originLocalizationMap k K n) Ideal.le_comap_map) := by
  have : IsLocalHom (algebraMap (OriginLocalization k n) (OriginLocalization K n)) :=
    originLocalizationMap_isLocalHom k K n
  have : Module.Flat (OriginLocalization k n) (OriginLocalization K n) :=
    originLocalizationMap_flat k K n
  have : Module.FaithfullyFlat (OriginLocalization k n) (OriginLocalization K n) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  apply Ideal.quotientMap_injective'
  exact (Ideal.comap_map_eq_self_of_faithfullyFlat (B := OriginLocalization K n) _).le

variable {k K n} {A : Type*} [CommRing A]

/-- Descend a regular localized quotient, with reconstruction and its coordinate map.
The tensor product here extends the localized source, not just the coefficient field. -/
theorem exists_finite_field_of_localized_presentation [Algebra.IsAlgebraic k K]
    (rs : List (OriginLocalization K n))
    (hreg : RingTheory.Sequence.IsRegular (OriginLocalization K n) rs)
    (e : (OriginLocalization K n ⧸ Ideal.ofList rs) ≃+* A) :
    ∃ E : IntermediateField k K, FiniteDimensional k E ∧
      ∃ qs : List (OriginLocalization E n), qs.map (originLocalizationMap E K n) = rs ∧
        qs.length = rs.length ∧ RingTheory.Sequence.IsRegular (OriginLocalization E n) qs ∧
        ∃ e' : (OriginLocalization K n ⊗[OriginLocalization E n]
            (OriginLocalization E n ⧸ Ideal.ofList qs)) ≃+* A,
          ∀ b a, e' (b ⊗ₜ Ideal.Quotient.mk _ a) =
            e (Ideal.Quotient.mk _ (originLocalizationMap E K n a * b)) := by
  obtain ⟨E, hE, qs, hqs, hlen, hreg⟩ :=
    exists_finite_field_of_localized_regular_list (k := k) hreg
  let eqv := (originQuotientBaseChangeEquiv E K n qs).toRingEquiv.trans
    ((Ideal.quotientEquivAlgOfEq (OriginLocalization K n)
      (congrArg Ideal.ofList hqs)).toRingEquiv.trans e)
  exact ⟨E, hE, qs, hqs, hlen, hreg, eqv, fun _ _ ↦ rfl⟩

end MvPolynomial
