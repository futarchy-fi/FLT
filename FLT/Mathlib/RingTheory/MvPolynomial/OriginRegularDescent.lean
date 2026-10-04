/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.MvPolynomial.OriginPresentationBaseChange
public import FLT.Mathlib.RingTheory.LocalRing.IdealGeneratorDescent
public import FLT.GroupScheme.PolynomialLocalParameterCriterion

/-! # Descending regular presentations at the rational polynomial origin -/

@[expose] public noncomputable section

namespace MvPolynomial

variable {k : Type*} [Field k] (K : Type*) [Field K] [Algebra k K] {n : ℕ}

/-- A square generating family after coefficient extension descends to regular
relations for an Artinian quotient of the original rational local ring. -/
theorem exists_regular_origin_relations_of_map_eq_span (I : Ideal (OriginLocalization k n))
    [IsArtinianRing (OriginLocalization k n ⧸ I)] [Nontrivial (OriginLocalization k n ⧸ I)]
    (v : Fin n → OriginLocalization K n)
    (hv : I.map (originLocalizationMap k K n) = Ideal.span (Set.range v)) :
    ∃ rs : List (OriginLocalization k n), rs.length = n ∧ Ideal.ofList rs = I ∧
      RingTheory.Sequence.IsRegular (OriginLocalization k n) rs := by
  let := (originLocalizationMap k K n).toAlgebra
  have : Module.Flat (OriginLocalization k n) (OriginLocalization K n) :=
    originLocalizationMap_flat k K n
  have : IsLocalHom (algebraMap (OriginLocalization k n) (OriginLocalization K n)) :=
    originLocalizationMap_isLocalHom k K n
  have : Module.Finite (OriginLocalization k n) I :=
    Module.Finite.of_fg (IsNoetherian.noetherian I)
  obtain ⟨rs, hlen, hrs⟩ := I.exists_ofList_of_map_eq_span (OriginLocalization K n) v hv
  have : IsArtinianRing (OriginLocalization k n ⧸ Ideal.ofList rs) := by rw [hrs]; infer_instance
  have : Nontrivial (OriginLocalization k n ⧸ Ideal.ofList rs) := by rw [hrs]; infer_instance
  exact ⟨rs, hlen, hrs, isRegular_parameters_at_rationalPoint (fun _ ↦ 0) rs hlen⟩

variable [Algebra.IsAlgebraic k K] {A : Type*} [CommRing A] [Algebra k A]
  [IsArtinianRing A] [Nontrivial A]

/-- For a specified original presentation, square geometric kernel generators suffice:
neither original relations nor their geometric regularity is assumed. -/
theorem exists_regular_presentation_of_originBaseChange_kernel
    (f : OriginLocalization k n →ₐ[k] A) (hf : Function.Surjective f)
    (v : Fin n → OriginLocalization K n)
    (hv : RingHom.ker (originPresentationBaseChange K f) = Ideal.span (Set.range v)) :
    ∃ rs : List (OriginLocalization k n), rs.length = n ∧
      RingHom.ker f = Ideal.ofList rs ∧
      RingTheory.Sequence.IsRegular (OriginLocalization k n) rs ∧
      ∃ e : (OriginLocalization k n ⧸ Ideal.ofList rs) ≃ₐ[k] A,
        ∀ x, e (Ideal.Quotient.mk _ x) = f x := by
  let e := Ideal.quotientKerAlgEquivOfSurjective hf
  have : IsArtinianRing (OriginLocalization k n ⧸ RingHom.ker f) :=
    e.symm.toRingEquiv.isArtinianRing
  have : Nontrivial (OriginLocalization k n ⧸ RingHom.ker f) := e.surjective.nontrivial
  rw [ker_originPresentationBaseChange K f hf] at hv
  obtain ⟨rs, hlen, hrs, hreg⟩ :=
    exists_regular_origin_relations_of_map_eq_span K (RingHom.ker f) v hv
  exact ⟨rs, hlen, hrs.symm, hreg,
    (Ideal.quotientEquivAlgOfEq k hrs).trans e, fun _ ↦ rfl⟩

end MvPolynomial
