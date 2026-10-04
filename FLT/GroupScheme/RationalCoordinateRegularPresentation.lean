/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.AugmentedPolynomialLocalParameters

/-! # Regular local presentations at a specified rational point -/

@[expose] public noncomputable section

namespace MvPolynomial

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A] [IsLocalRing A] {n : ℕ}

/-- The maximal ideal of a rational local algebra pulls back to its coordinate point. -/
theorem comap_maximalIdeal_aeval_at_point (ε : A →ₐ[k] k) (x : Fin n → A) :
    (IsLocalRing.maximalIdeal A).comap (aeval (R := k) x) =
      rationalPointIdeal (fun i ↦ ε (x i)) := by
  have he : RingHom.ker ε = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective ε
      (fun c ↦ ⟨algebraMap k A c, ε.commutes c⟩))
  have hcomp : ε.comp (aeval x) = aeval (fun i ↦ ε (x i)) := by ext i; simp
  rw [← he]
  change RingHom.ker (ε.comp (aeval x)) = _
  rw [hcomp]

/-- A square local presentation at any rational point is regular when its quotient is Artinian. -/
theorem isRegular_localized_point_parameters (ε : A →ₐ[k] k) (x : Fin n → A)
    (rs : List (aeval (R := k) x).localizedSource) (hlen : rs.length = n)
    [IsArtinianRing ((aeval (R := k) x).localizedSource ⧸ Ideal.ofList rs)]
    [Nontrivial ((aeval (R := k) x).localizedSource ⧸ Ideal.ofList rs)] :
    RingTheory.Sequence.IsRegular (aeval (R := k) x).localizedSource rs := by
  have key (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime]
      (hP : P = rationalPointIdeal (fun i ↦ ε (x i)))
      (ss : List (Localization.AtPrime P)) (hlen : ss.length = n)
      [IsArtinianRing (Localization.AtPrime P ⧸ Ideal.ofList ss)]
      [Nontrivial (Localization.AtPrime P ⧸ Ideal.ofList ss)] :
      RingTheory.Sequence.IsRegular (Localization.AtPrime P) ss := by
    subst P
    exact isRegular_parameters_at_rationalPoint _ ss hlen
  exact @key _ inferInstance (comap_maximalIdeal_aeval_at_point ε x) rs hlen
    ‹IsArtinianRing ((aeval (R := k) x).localizedSource ⧸ Ideal.ofList rs)›
    ‹Nontrivial ((aeval (R := k) x).localizedSource ⧸ Ideal.ofList rs)›

/-- A specified square polynomial kernel supplies regular localized relations and the
quotient isomorphism in the original coordinates. -/
theorem exists_local_regular_presentation_of_square_kernel [IsArtinianRing A]
    (ε : A →ₐ[k] k) (x : Fin n → A) (hs : Function.Surjective (aeval (R := k) x))
    (r : Fin n → MvPolynomial (Fin n) k)
    (hr : RingHom.ker (aeval (R := k) x) = Ideal.span (Set.range r)) :
    ∃ rs : List (aeval (R := k) x).localizedSource,
      rs.length = n ∧
      RingHom.ker (aeval (R := k) x).localizeAtMaximal = Ideal.ofList rs ∧
      RingTheory.Sequence.IsRegular (aeval (R := k) x).localizedSource rs ∧
      ∃ e : ((aeval (R := k) x).localizedSource ⧸ Ideal.ofList rs) ≃ₐ[k] A,
        ∀ q, e (Ideal.Quotient.mk _ q) = (aeval (R := k) x).localizeAtMaximal q := by
  let f := aeval (R := k) x
  let rs := (List.finRange n).map fun i ↦ algebraMap (MvPolynomial (Fin n) k) f.localizedSource
    (r i)
  have hker : RingHom.ker f.localizeAtMaximal = Ideal.ofList rs := by
    rw [f.ker_localizeAtMaximal_eq_span r hr]
    congr 1
    ext q
    simp [rs]
  let e : (f.localizedSource ⧸ Ideal.ofList rs) ≃ₐ[k] A :=
    (Ideal.quotientEquivAlgOfEq k hker.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (f.localizeAtMaximal_surjective hs))
  have : IsArtinianRing (f.localizedSource ⧸ Ideal.ofList rs) := e.symm.toRingEquiv.isArtinianRing
  have : Nontrivial (f.localizedSource ⧸ Ideal.ofList rs) := e.surjective.nontrivial
  exact ⟨rs, by simp [rs], hker,
    isRegular_localized_point_parameters ε x rs (by simp [rs]), e, fun _ ↦ rfl⟩

end MvPolynomial
