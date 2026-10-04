/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Localization.PrincipalIdealBaseChange
public import FLT.Mathlib.RingTheory.MvPolynomial.BaseChangePresentation
public import FLT.Mathlib.RingTheory.MvPolynomial.FiniteFibreParameterRegularity

/-! # Simultaneous fibre regularity on a square principal presentation -/

@[expose] public noncomputable section

namespace MvPolynomial

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [Module.Finite R A] {d : ℕ}

/-- A square principal presentation of a finite algebra is regular at every point
of every field-valued fibre on that principal open. The base ring is arbitrary. -/
theorem isRegular_principal_presentation_fibre
    (f : MvPolynomial (Fin d) R →ₐ[R] A) (hf : Function.Surjective f)
    (a : MvPolynomial (Fin d) R) (rs : List (MvPolynomial (Fin d) R)) (hlen : rs.length = d)
    (hgen : Ideal.ofList (rs.map (algebraMap _ (Localization.Away a))) =
      (RingHom.ker f).map (algebraMap _ (Localization.Away a)))
    (k : Type*) [Field k] [Algebra R k]
    (P : Ideal (MvPolynomial (Fin d) k)) [P.IsPrime]
    (hP : RingHom.ker (baseChangePresentation k f) ≤ P)
    (ha : map (algebraMap R k) a ∉ P) :
    RingTheory.Sequence.IsRegular (Localization.AtPrime P)
      ((rs.map (map (algebraMap R k))).map (algebraMap _ (Localization.AtPrime P))) := by
  let φ := (algebraMap (MvPolynomial (Fin d) k) (Localization.AtPrime P)).comp
    (map (algebraMap R k))
  have hu : IsUnit (φ a) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P) P _).mpr ha
  have he : (Ideal.ofList rs).map φ = (RingHom.ker f).map φ :=
    Ideal.map_eq_of_isUnit_of_away_eq _ _ a (by rwa [Ideal.map_ofList]) φ hu
  have hg : Ideal.ofList
      ((rs.map (map (algebraMap R k))).map (algebraMap _ (Localization.AtPrime P))) =
      (RingHom.ker (baseChangePresentation k f)).map (algebraMap _ (Localization.AtPrime P)) := by
    rw [← Ideal.map_ofList, ← Ideal.map_ofList, Ideal.map_map,
      ker_baseChangePresentation k f hf, Ideal.map_map]
    exact he
  exact isRegular_finite_kernel_atPrime (baseChangePresentation k f)
    (baseChangePresentation_surjective k f hf) P hP _ (by simpa using hlen) hg

end MvPolynomial
