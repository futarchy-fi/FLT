/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Localization.ArtinianPresentation
public import FLT.Mathlib.RingTheory.MvPolynomial.CoefficientPresentation
public import FLT.Mathlib.RingTheory.MvPolynomial.GeometricParameterRegularity
public import FLT.Mathlib.RingTheory.MvPolynomial.ResidueGeometricPoint

/-! # Every square kernel list for a finite field algebra is regular locally -/

@[expose] public noncomputable section

open scoped TensorProduct

namespace MvPolynomial

variable {k K A : Type*} [Field k] [Field K] [Algebra k K]
  [CommRing A] [Algebra k A] [Module.Finite k A] {n : ℕ}

/-- A specified square list generating the local kernel of a finite algebra
is regular at any contracted geometric point. -/
theorem isRegular_finite_kernel_at_geometricPoint
    (f : MvPolynomial (Fin n) k →ₐ[k] A) (hf : Function.Surjective f) (a : Fin n → K)
    (hP : RingHom.ker f ≤ (rationalPointIdeal a).comap (map (algebraMap k K)))
    (rs : List (GeometricPointSource k K a)) (hlen : rs.length = n)
    (hgen : Ideal.ofList rs = (RingHom.ker f).map (algebraMap _ (GeometricPointSource k K a))) :
    RingTheory.Sequence.IsRegular (GeometricPointSource k K a) rs := by
  let g := coefficientPresentation K f
  have hg : Function.Surjective g := coefficientPresentation_surjective K f hf
  have hQ : RingHom.ker g ≤ rationalPointIdeal a := by
    rw [ker_coefficientPresentation K f hf]
    exact Ideal.map_le_iff_le_comap.mpr hP
  have he : Ideal.ofList (rs.map (geometricPointLocalizationMap k K a)) =
      (RingHom.ker g).map (algebraMap _ (Localization.AtPrime (rationalPointIdeal a))) := by
    rw [← Ideal.map_ofList, hgen, map_ideal_geometricPointLocalization,
      ker_coefficientPresentation K f hf]
  have : IsArtinianRing (K ⊗[k] A) := IsArtinianRing.of_finite K _
  have : IsArtinianRing (Localization.AtPrime (rationalPointIdeal a) ⧸
      Ideal.ofList (rs.map (geometricPointLocalizationMap k K a))) := by
    rw [he]
    exact g.isArtinianRing_quotient_localized_kernel hg _ hQ
  have hle : (RingHom.ker g).map (algebraMap _ (Localization.AtPrime (rationalPointIdeal a))) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime (rationalPointIdeal a)) := by
    exact (Ideal.map_mono hQ).trans_eq (IsLocalization.AtPrime.map_eq_maximalIdeal _ _)
  have : Nontrivial (Localization.AtPrime (rationalPointIdeal a) ⧸
      Ideal.ofList (rs.map (geometricPointLocalizationMap k K a))) := by
    apply Ideal.Quotient.nontrivial_iff.mpr
    rw [he]
    exact (hle.trans_lt (IsLocalRing.maximalIdeal.isMaximal _).lt_top).ne
  exact isRegular_parameters_at_geometricPoint a rs hlen

/-- At every prime over a finite-algebra presentation kernel, every square
list generating that local kernel is regular, in its specified order. -/
theorem isRegular_finite_kernel_atPrime
    (f : MvPolynomial (Fin n) k →ₐ[k] A) (hf : Function.Surjective f)
    (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime] (hP : RingHom.ker f ≤ P)
    (rs : List (Localization.AtPrime P)) (hlen : rs.length = n)
    (hgen : Ideal.ofList rs = (RingHom.ker f).map (algebraMap _ (Localization.AtPrime P))) :
    RingTheory.Sequence.IsRegular (Localization.AtPrime P) rs := by
  obtain ⟨y, hy⟩ := exists_geometric_point_over_prime f hf P hP
  let a := fun i ↦ y (f (X i))
  have h (Q : Ideal (MvPolynomial (Fin n) k)) [Q.IsPrime]
      (hQ : Q = (rationalPointIdeal a).comap
        (map (algebraMap k (AlgebraicClosure P.ResidueField))))
      (v : List (Localization.AtPrime Q)) (hv : v.length = n)
      (hI : Ideal.ofList v = (RingHom.ker f).map (algebraMap _ (Localization.AtPrime Q)))
      (hk : RingHom.ker f ≤ Q) : RingTheory.Sequence.IsRegular (Localization.AtPrime Q) v := by
    subst Q
    exact isRegular_finite_kernel_at_geometricPoint f hf a hk v hv hI
  exact h P hy.symm rs hlen hgen hP

end MvPolynomial
