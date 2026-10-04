/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PolynomialLocalParameterCriterion
public import FLT.Mathlib.RingTheory.LocalizedPresentation

/-! # Regular parameters in the local source of an augmented presentation -/

@[expose] public noncomputable section

namespace MvPolynomial

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A] [IsLocalRing A] {n : ℕ}

/-- Augmentation coordinates pull the maximal ideal back to the rational origin. -/
theorem comap_maximalIdeal_aeval_of_augmentation (ε : A →ₐ[k] k) (x : Fin n → A)
    (hx : ∀ i, ε (x i) = 0) :
    (IsLocalRing.maximalIdeal A).comap (aeval (R := k) x) =
      rationalPointIdeal (fun _ : Fin n ↦ (0 : k)) := by
  have he : RingHom.ker ε = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective ε
      (fun c ↦ ⟨algebraMap k A c, ε.commutes c⟩))
  have hcomp : ε.comp (aeval x) = aeval (fun _ : Fin n ↦ (0 : k)) := by
    ext i
    simpa using hx i
  rw [← he]
  change RingHom.ker (ε.comp (aeval x)) = _
  rw [hcomp]

/-- The local source of an augmented n-coordinate presentation satisfies the parameter theorem. -/
theorem isRegular_localized_augmentation_parameters (ε : A →ₐ[k] k) (x : Fin n → A)
    (hx : ∀ i, ε (x i) = 0) (rs : List (aeval (R := k) x).localizedSource)
    (hlen : rs.length = n)
    [IsArtinianRing ((aeval (R := k) x).localizedSource ⧸ Ideal.ofList rs)]
    [Nontrivial ((aeval (R := k) x).localizedSource ⧸ Ideal.ofList rs)] :
    RingTheory.Sequence.IsRegular (aeval (R := k) x).localizedSource rs := by
  have key (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime]
      (hP : P = rationalPointIdeal (fun _ : Fin n ↦ (0 : k)))
      (ss : List (Localization.AtPrime P)) (hlen : ss.length = n)
      [IsArtinianRing (Localization.AtPrime P ⧸ Ideal.ofList ss)]
      [Nontrivial (Localization.AtPrime P ⧸ Ideal.ofList ss)] :
      RingTheory.Sequence.IsRegular (Localization.AtPrime P) ss := by
    subst P
    exact isRegular_parameters_at_rationalPoint (fun _ ↦ 0) ss hlen
  exact @key _ inferInstance (comap_maximalIdeal_aeval_of_augmentation ε x hx) rs hlen
    ‹IsArtinianRing ((aeval (R := k) x).localizedSource ⧸ Ideal.ofList rs)›
    ‹Nontrivial ((aeval (R := k) x).localizedSource ⧸ Ideal.ofList rs)›

end MvPolynomial
