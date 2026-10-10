/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBasisBaseChangeCover
public import FLT.Mazur.HilbertIntrinsicBasisGlobal

/-!
# Affine tests of the intrinsic polynomial basis scheme

An affine scalar-extension map factors uniquely through the intrinsic open
exactly when the actual extended polynomial ideal has the prescribed basis.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Type u) (d : ℕ)
variable (w : Fin d → MvPolynomial I R)
variable (S : Type u) [CommRing S] [Algebra R S] (J : Ideal (MvPolynomial I S))
variable [Module.FinitePresentation S (MvPolynomial I S ⧸ J)]
variable [Module.Flat S (MvPolynomial I S ⧸ J)]
variable (T : Type u) [CommRing T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

/-- Testing every point of an affine base change detects a global prescribed quotient basis. -/
theorem polynomialBasisOpen_affineTest_iff :
    (∀ p : PrimeSpectrum T, PrimeSpectrum.comap (algebraMap S T) p ∈
      polynomialBasisOpen R I d w S J) ↔
    ∃ b : Module.Basis (Fin d) T
      (MvPolynomial I T ⧸ J.map (MvPolynomial.map (algebraMap S T))),
      ∀ i, polynomialBasisTuple R I d w T
        (J.map (MvPolynomial.map (algebraMap S T))) i = b i := by
  let _ := polynomialQuotient_finitePresentation_baseChange I S J T
  have h := intrinsicBasisOpen_eq_top_iff (R := T)
    (polynomialBasisTuple R I d w T (J.map (MvPolynomial.map (algebraMap S T))))
  rw [show intrinsicBasisOpen (R := T) (polynomialBasisTuple R I d w T
      (J.map (MvPolynomial.map (algebraMap S T)))) =
      polynomialBasisOpen R I d w T (J.map (MvPolynomial.map (algebraMap S T))) from rfl,
    polynomialBasisOpen_preimage R I d w S J T] at h
  rw [← show (∃ b : Module.Basis (Fin d) T
      (MvPolynomial I T ⧸ J.map (MvPolynomial.map (algebraMap S T))),
      ∀ i, b i = polynomialBasisTuple R I d w T
        (J.map (MvPolynomial.map (algebraMap S T))) i) ↔ _ from
    exists_congr (fun _ ↦ forall_congr' (fun _ ↦ eq_comm))]
  rw [← h]
  exact ⟨fun hp ↦ top_unique (fun p _ ↦ hp p), fun hp p ↦ hp.ge trivial⟩

/-- Factoring through the actual basis open is equivalent to the prescribed-basis condition. -/
theorem polynomialBasisScheme_affineFactorization_iff :
    (∃! f : Spec (.of T) ⟶ polynomialBasisScheme R I d w S J,
      f ≫ Scheme.Opens.ι (X := Spec (.of S)) (polynomialBasisOpen R I d w S J) =
        Spec.map (CommRingCat.ofHom (algebraMap S T))) ↔
    ∃ b : Module.Basis (Fin d) T
      (MvPolynomial I T ⧸ J.map (MvPolynomial.map (algebraMap S T))),
      ∀ i, polynomialBasisTuple R I d w T
        (J.map (MvPolynomial.map (algebraMap S T))) i = b i := by
  rw [← polynomialBasisOpen_affineTest_iff R I d w S J T]
  constructor
  · rintro ⟨f, hf, _⟩ p
    have h : (f ≫ Scheme.Opens.ι (X := Spec (.of S))
        (polynomialBasisOpen R I d w S J)) p ∈ polynomialBasisOpen R I d w S J :=
      (f p).property
    rw [hf] at h
    exact h
  · intro h
    let i := Scheme.Opens.ι (X := Spec (.of S)) (polynomialBasisOpen R I d w S J)
    let g := Spec.map (CommRingCat.ofHom (algebraMap S T))
    have hr : Set.range g ⊆ Set.range i := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨p, rfl⟩
      exact h p
    exact ⟨IsOpenImmersion.lift i g hr, IsOpenImmersion.lift_fac i g hr,
      fun f hf ↦ IsOpenImmersion.lift_uniq i g hr f hf⟩

end FLT.Mazur.HilbertChart
