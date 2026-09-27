/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.IntegralEtaleModelRamification
public import Mathlib.RingTheory.Smooth.Fiber
public import Mathlib.RingTheory.Smooth.IntegralClosure

/-!
# Integral étale coordinate algebras

For a finite continuous Galois module unramified outside `S`, the integral closure
of `ℤ[1/S]` in its generic coordinate algebra is finite étale. The proof first
localizes the rings of integers of its field factors, then assembles the factors.
The generic-fibre algebra comparison, integral counit and integral antipode are
constructed in `IntegralCoordinateAlgebra`; the Hopf structure is assembled in
`IntegralEtaleModel` using `IntegralHopfAlgebra`.
-/

@[expose] public noncomputable section

open scoped TensorProduct NumberField

namespace ThreeAdicPlan
attribute [local instance 100000] Algebra.toSMul Algebra.toModule
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Local unramifiedness away from an element implies unramifiedness of its localization. -/
theorem formallyUnramifiedAway (R A B : Type) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    (a : A) [IsLocalization.Away a B]
    (h : ∀ (P : Ideal A) [P.IsPrime], a ∉ P → Algebra.IsUnramifiedAt R P) :
    Algebra.FormallyUnramified R B := by
  apply Algebra.formallyUnramified_iff_forall.mpr
  intro Q
  let P := Q.asIdeal.under A
  have ha : a ∉ P :=
    Q.asIdeal.notMem_of_isUnit (IsLocalization.Away.algebraMap_isUnit a)
  let : Algebra.IsUnramifiedAt R P := h P ha
  let : IsLocalization.AtPrime (Localization.AtPrime Q.asIdeal) P :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.powers a) (Localization.AtPrime Q.asIdeal) Q.asIdeal
  exact Algebra.FormallyUnramified.of_equiv
    ((IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P)
      (Localization.AtPrime Q.asIdeal)).restrictScalars R)

/-- The prime-place conventions in the inertia predicate and Mathlib agree. -/
theorem primePlace_eq (p : ℕ) (hp : p.Prime) :
    hp.toHeightOneSpectrumRingOfIntegersRat =
      (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp⟩ := by
  apply IsDedekindDomain.HeightOneSpectrum.ext
  change Ideal.comap Rat.ringOfIntegersEquiv (Ideal.span {(p : ℤ)}) =
    Ideal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm (Ideal.span {(p : ℤ)})
  rw [Ideal.map_symm]
  congr 1
  ext x
  exact (Rat.IsIntegralClosure.intEquiv_apply_eq_ringOfIntegersEquiv x).symm

/-- Arithmetic unramifiedness outside `S` gives formal unramifiedness where the product
of the primes in `S` is invertible. -/
@[nolint unusedArguments]
theorem numberFieldUnramifiedAt (F : Type) [Field F] [Algebra ℚ F] [NumberField F]
    (S : Finset ℕ)
    (h : ∀ (p : ℕ) (hp : p.Prime), p ∉ S →
      Algebra.IsUnramifiedIn (𝓞 F) hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)
    (P : Ideal (𝓞 F)) [P.IsPrime] (hD : (∏ p ∈ S, (p : 𝓞 F)) ∉ P) :
    Algebra.IsUnramifiedAt ℤ P := by
  let : Algebra.FormallyUnramified ℤ (𝓞 ℚ) :=
    Algebra.FormallyUnramified.of_surjective (Algebra.ofId ℤ (𝓞 ℚ))
      (Rat.int_algebraMap_surjective (𝓞 ℚ))
  suffices Algebra.IsUnramifiedAt (𝓞 ℚ) P from
    Algebra.FormallyUnramified.comp ℤ (𝓞 ℚ) (Localization.AtPrime P)
  by_cases hP : P = ⊥
  · subst P
    exact Algebra.isUnramifiedAt_bot
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) :=
    ⟨P.under (𝓞 ℚ), inferInstance, Ideal.IsIntegral.under_ne_bot (𝓞 ℚ) hP⟩
  let q := Rat.HeightOneSpectrum.primesEquiv v
  have he : q.property.toHeightOneSpectrumRingOfIntegersRat = v :=
    (primePlace_eq q.val q.property).trans
      (Rat.HeightOneSpectrum.primesEquiv.symm_apply_apply v)
  have hq : (q.val : 𝓞 F) ∈ P := by
    have hmem : (q.val : 𝓞 ℚ) ∈ q.property.toHeightOneSpectrumRingOfIntegersRat.asIdeal := by
      change Rat.ringOfIntegersEquiv (q.val : 𝓞 ℚ) ∈ Ideal.span {(q.val : ℤ)}
      simp
    rw [he] at hmem
    change algebraMap (𝓞 ℚ) (𝓞 F) (q.val : 𝓞 ℚ) ∈ P at hmem
    simpa using hmem
  have hqS : q.val ∉ S := by
    intro hqS
    exact hD (Ideal.IsPrime.prod_mem_iff.mpr ⟨q.val, hqS, hq⟩)
  have hunr := h q.val q.property hqS
  rw [he] at hunr
  exact hunr P inferInstance inferInstance

/-- The ring of `S`-integers of a number field unramified outside `S` is étale over `ℤ[1/S]`. -/
@[nolint unusedArguments]
theorem numberFieldIntegralClosureEtale (F : Type) [Field F] [Algebra ℚ F] [NumberField F]
    (S : Finset ℕ) [Fact (∀ p ∈ S, p.Prime)]
    [Algebra (ZInvPrimes S) F] [IsScalarTower (ZInvPrimes S) ℚ F]
    (h : ∀ (p : ℕ) (hp : p.Prime), p ∉ S →
      Algebra.IsUnramifiedIn (𝓞 F) hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal) :
    Algebra.Etale (ZInvPrimes S) (integralClosure (ZInvPrimes S) F) := by
  let R := ZInvPrimes S
  let B := R ⊗[ℤ] (𝓞 F)
  let : Algebra (𝓞 F) B := Algebra.TensorProduct.rightAlgebra
  let : IsLocalization.Away (∏ p ∈ S, (p : 𝓞 F)) B := by
    have hi : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 F)
        (Submonoid.powers (∏ p ∈ S, (p : ℤ)))) B := inferInstance
    simpa [Algebra.algebraMapSubmonoid, Submonoid.map_powers, map_prod] using hi
  let : Algebra.FormallyUnramified ℤ B :=
    formallyUnramifiedAway ℤ (𝓞 F) B (∏ p ∈ S, (p : 𝓞 F))
      (numberFieldUnramifiedAt F S h)
  let : Algebra.FormallyUnramified R B :=
    Algebra.FormallyUnramified.of_restrictScalars ℤ R B
  let : IsNoetherianRing R := inferInstanceAs (IsNoetherianRing (ZInvPrimes S))
  let : Module.Finite R B := inferInstanceAs (Module.Finite R (R ⊗[ℤ] (𝓞 F)))
  let : Algebra.FinitePresentation R B :=
    (Algebra.FinitePresentation.of_finiteType (R := R) (A := B)).mp inferInstance
  let : Algebra.Etale R B := Algebra.Etale.of_formallyUnramified_of_flat (R := R) (S := B)
  let : IsScalarTower ℤ R F := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  let e : B ≃ₐ[R] integralClosure R F :=
    (AlgEquiv.ofBijective (TensorProduct.toIntegralClosure ℤ R F)
      (TensorProduct.toIntegralClosure_bijective_of_isLocalization
        (Submonoid.powers (∏ p ∈ S, (p : ℤ))))).trans
      (AlgEquiv.mapIntegralClosure
        (IsLocalization.algebraLid (Submonoid.powers (∏ p ∈ S, (p : ℤ))) R F))
  exact Algebra.Etale.of_equiv (R := R) (A := B) e

namespace FiniteContinuousGaloisModule

/-- The canonical integral coordinate algebra is finite étale away from the exceptional primes.
Finiteness is supplied by `integralCoordinateAlgebraFinite`. -/
theorem integralCoordinateAlgebraEtale (S : Finset ℕ) [Fact (∀ p ∈ S, p.Prime)]
    (W : FiniteContinuousGaloisModule) (h : UnramifiedOutside S W) :
    Algebra.Etale (ZInvPrimes S) (W.IntegralCoordinateAlgebra S) := by
  let R := ZInvPrimes S
  let A := W.GenericCoordinateAlgebra
  let : IsReduced A := Algebra.FormallyUnramified.isReduced_of_field ℚ A
  let : IsArtinianRing A := .of_finite ℚ A
  let : IsScalarTower R ℚ A := W.genericCoordinateAlgebraScalarTower S
  let F (m : MaximalSpectrum A) := A ⧸ m.asIdeal
  let (m : MaximalSpectrum A) : Field (F m) := Ideal.Quotient.field m.asIdeal
  let (m : MaximalSpectrum A) : Algebra ℚ (F m) := Ideal.Quotient.algebra ℚ
  let (m : MaximalSpectrum A) : IsScalarTower R ℚ (F m) := inferInstance
  let (m : MaximalSpectrum A) : NumberField (F m) := NumberField.of_module_finite ℚ (F m)
  let (m : MaximalSpectrum A) : Module.Finite R (integralClosure R (F m)) :=
    integralClosureFinite R ℚ (F m)
  let (m : MaximalSpectrum A) : Algebra.Etale R (integralClosure R (F m)) :=
    numberFieldIntegralClosureEtale (F m) S
      (W.fieldFactor_isUnramifiedIn (F m) (Ideal.Quotient.mkₐ ℚ m.asIdeal)
        Ideal.Quotient.mk_surjective h)
  let e : A ≃ₐ[R] ∀ m : MaximalSpectrum A, F m :=
    (IsArtinianRing.equivPi A).restrictScalars R
  let f : integralClosure R A →ₐ[R] ∀ m : MaximalSpectrum A, integralClosure R (F m) :=
    AlgHom.pi fun m ↦ ((Pi.evalAlgHom R F m).comp e.toAlgHom).mapIntegralClosure
  have hi : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply e.injective
    funext m
    exact congrArg (fun z ↦ (z m : F m)) hxy
  have hs : Function.Surjective f := by
    let g : (∀ m : MaximalSpectrum A, integralClosure R (F m)) →ₐ[R] ∀ m, F m :=
      AlgHom.pi fun m ↦ (integralClosure R (F m)).val.comp
        (Pi.evalAlgHom R (fun m ↦ integralClosure R (F m)) m)
    intro x
    refine ⟨⟨e.symm (g x), ?_⟩, ?_⟩
    · exact (Algebra.IsIntegral.isIntegral (R := R) x).map (e.symm.toAlgHom.comp g)
    · funext m
      apply Subtype.ext
      change e (e.symm (g x)) m = (x m : F m)
      rw [e.apply_symm_apply]
      rfl
  exact Algebra.Etale.of_equiv (R := R)
    (A := ∀ m : MaximalSpectrum A, integralClosure R (F m)) (AlgEquiv.ofBijective f ⟨hi, hs⟩).symm

end FiniteContinuousGaloisModule
end ThreeAdicPlan
