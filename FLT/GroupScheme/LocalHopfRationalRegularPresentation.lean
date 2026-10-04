/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.LocalHopfRegularPresentation

/-! # A finite local Hopf algebra as a regular quotient of a rational polynomial local ring -/

@[expose] public noncomputable section

universe u

namespace HopfAlgebra

open MvPolynomial

variable {k A : Type u} [Field k] [CommRing A] [HopfAlgebra k A]
  [IsLocalRing A] [Module.Finite k A]
  (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]

include p

/-- The local complete-intersection presentation with the polynomial origin made explicit. -/
theorem exists_rational_local_regular_presentation :
    ∃ (n : ℕ) (rs : List (Localization.AtPrime (rationalPointIdeal (fun _ : Fin n ↦ (0 : k))))),
      rs.length = n ∧
      RingTheory.Sequence.IsRegular
        (Localization.AtPrime (rationalPointIdeal (fun _ : Fin n ↦ (0 : k)))) rs ∧
      Nonempty (((Localization.AtPrime (rationalPointIdeal (fun _ : Fin n ↦ (0 : k)))) ⧸
        Ideal.ofList rs) ≃ₐ[k] A) := by
  obtain ⟨P, hx, r, ⟨e⟩, hreg⟩ := exists_minimal_local_regular_presentation (k := k) (A := A) p
  let n := Module.finrank k (RingHom.ker (Bialgebra.counitAlgHom k A)).Cotangent
  let f := aeval (R := k) P.val
  have hspan : Ideal.ofList ((List.finRange n).map r) = Ideal.span (Set.range r) :=
    congrArg Ideal.span (Set.ext fun q ↦ by simp)
  have hex : ∃ rs : List f.localizedSource,
      rs.length = n ∧ RingTheory.Sequence.IsRegular f.localizedSource rs ∧
      Nonempty ((f.localizedSource ⧸ Ideal.ofList rs) ≃ₐ[k] A) :=
    ⟨(List.finRange n).map r, by simp, hreg,
      ⟨(Ideal.quotientEquivAlgOfEq k hspan).trans e⟩⟩
  have hpoint := comap_maximalIdeal_aeval_of_augmentation (Bialgebra.counitAlgHom k A) P.val hx
  have key (Q : Ideal (MvPolynomial (Fin n) k)) [Q.IsPrime]
      (hQ : Q = rationalPointIdeal (fun _ : Fin n ↦ (0 : k)))
      (h : ∃ rs : List (Localization.AtPrime Q), rs.length = n ∧
        RingTheory.Sequence.IsRegular (Localization.AtPrime Q) rs ∧
        Nonempty ((Localization.AtPrime Q ⧸ Ideal.ofList rs) ≃ₐ[k] A)) :
      ∃ rs : List (Localization.AtPrime (rationalPointIdeal (fun _ : Fin n ↦ (0 : k)))),
        rs.length = n ∧ RingTheory.Sequence.IsRegular
          (Localization.AtPrime (rationalPointIdeal (fun _ : Fin n ↦ (0 : k)))) rs ∧
        Nonempty ((Localization.AtPrime (rationalPointIdeal (fun _ : Fin n ↦ (0 : k))) ⧸
          Ideal.ofList rs) ≃ₐ[k] A) := by
    subst Q
    exact h
  exact ⟨n, key _ hpoint hex⟩

end HopfAlgebra
