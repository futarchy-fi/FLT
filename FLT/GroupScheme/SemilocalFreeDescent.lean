/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Descent of finite freeness over semilocal rings
-/

@[expose] public noncomputable section

open TensorProduct Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

set_option backward.isDefEq.respectTransparency.types false in
/-- A family whose image is a basis over the residue field generates a finite
module over a local ring. -/
theorem IsLocalRing.linearCombination_surjective_of_residueField
    [IsLocalRing R] [Module.Finite R M] {ι : Type*} (v : ι → M)
    (h : Function.Bijective (Finsupp.linearCombination (IsLocalRing.ResidueField R)
      (TensorProduct.mk R (IsLocalRing.ResidueField R) M 1 ∘ v))) :
    Function.Surjective (Finsupp.linearCombination R v) := by
  rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
  refine IsLocalRing.span_eq_top_of_tmul_eq_basis _ (Basis.mk h.1 ?_) fun _ ↦ ?_
  · simpa only [top_le_iff, ← Finsupp.range_linearCombination, LinearMap.range_eq_top] using h.2
  · simp

/-- A finite module over a semilocal ring with constant residue dimension `n`
has a generating family of size `n`. -/
theorem Module.exists_generators_of_finrank_eq [Finite (MaximalSpectrum R)] [Module.Finite R M]
    (n : ℕ) (rk : ∀ P : MaximalSpectrum R,
      finrank (R ⧸ P.1) ((R ⧸ P.1) ⊗[R] M) = n) :
    ∃ v : Fin n → M, Function.Surjective (Finsupp.linearCombination R v) := by
  let := @Ideal.Quotient.field
  have b' (P) := Module.finBasisOfFinrankEq _ _ (rk P)
  choose b hb using fun i ↦ Ideal.pi_tensorProductMk_quotient_surjective M _
    (fun _ _ ne ↦ Ideal.isCoprime_of_isMaximal (MaximalSpectrum.ext_iff.ne.mp ne)) (b' · i)
  refine ⟨b, surjective_of_isLocalized_maximal
    _ (fun P _ ↦ Finsupp.mapRange.linearMap (Algebra.linearMap R (Localization P.primeCompl)))
    _ (fun P _ ↦ TensorProduct.mk R (Localization P.primeCompl) M 1) _ fun P _ ↦ ?_⟩
  rw [IsLocalizedModule.map_linearCombination, LinearMap.coe_restrictScalars]
  apply IsLocalRing.linearCombination_surjective_of_residueField
  rw [← (AlgebraTensorModule.cancelBaseChange _ _ P.ResidueField ..).comp_bijective,
    ← (AlgebraTensorModule.cancelBaseChange R (R ⧸ P) P.ResidueField ..).symm.comp_bijective]
  convert! ((b' ⟨P, ‹_›⟩).repr.lTensor _ ≪≫ₗ finsuppScalarRight _ _ P.ResidueField _).symm.bijective
  refine funext fun r ↦ Finsupp.induction_linear r (by simp) (by simp +contextual) fun _ _ ↦ ?_
  simp [smul_tmul', ← funext_iff.mp (hb _)]

/-- Freeness descends along an injective scalar extension when the residue
dimensions equal the rank after extension. No flatness of the extension is assumed. -/
theorem Module.free_of_free_baseChange_of_finrank_eq
    (S : Type*) [CommRing S] [Nontrivial S] [Algebra R S] [FaithfulSMul R S]
    [Finite (MaximalSpectrum R)] [Module.Finite R M] [Module.Free S (S ⊗[R] M)]
    (rk : ∀ P : MaximalSpectrum R,
      finrank (R ⧸ P.1) ((R ⧸ P.1) ⊗[R] M) = finrank S (S ⊗[R] M)) :
    Module.Free R M := by
  let : Nontrivial R := (algebraMap R S).domain_nontrivial
  let n := finrank S (S ⊗[R] M)
  obtain ⟨v, hv⟩ := Module.exists_generators_of_finrank_eq (M := M) n rk
  let φ := Finsupp.linearCombination R v
  have hφ : Function.Surjective φ := hv
  have hψ : Function.Bijective (φ.baseChange S) := by
    apply OrzechProperty.bijective_of_surjective_of_finrank_le (φ.baseChange S)
      (φ.lTensor_surjective S hφ)
    simp [n]
  have hi : Function.Injective φ := by
    intro x y hxy
    apply Module.Flat.tensorProduct_mk_injective R (Fin n →₀ R) S
    apply hψ.1
    simpa using congrArg (fun z ↦ (1 : S) ⊗ₜ[R] z) hxy
  exact Module.Free.of_equiv (LinearEquiv.ofBijective φ ⟨hi, hφ⟩)

/-- Over an injective integral extension, the residue dimensions of a module
whose scalar extension is free equal its rank after extension. -/
theorem Module.finrank_residue_eq_of_free_baseChange
    (S : Type*) [CommRing S] [Nontrivial S] [Algebra R S] [FaithfulSMul R S]
    [Algebra.IsIntegral R S] [Module.Free S (S ⊗[R] M)]
    (P : Ideal R) [P.IsMaximal] :
    finrank (R ⧸ P) ((R ⧸ P) ⊗[R] M) = finrank S (S ⊗[R] M) := by
  let := @Ideal.Quotient.field
  let C := (R ⧸ P) ⊗[R] S
  have hP : P.map (algebraMap R S) ≠ ⊤ := by
    rw [Ne, Ideal.map_eq_top_iff (algebraMap R S)
      (FaithfulSMul.algebraMap_injective R S) (algebraMap_isIntegral_iff.mpr inferInstance)]
    exact Ideal.IsMaximal.ne_top ‹_›
  let : Nontrivial (S ⧸ P.map (algebraMap R S)) := Ideal.Quotient.nontrivial_iff.mpr hP
  let : Nontrivial C :=
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S P).symm.toEquiv.nontrivial
  let : Algebra S C := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower R S C := Algebra.TensorProduct.right_isScalarTower
  calc
    finrank (R ⧸ P) ((R ⧸ P) ⊗[R] M)
        = finrank C (C ⊗[R ⧸ P] ((R ⧸ P) ⊗[R] M)) :=
      (Module.finrank_baseChange (R := C)).symm
    _ = finrank C (C ⊗[R] M) :=
      (AlgebraTensorModule.cancelBaseChange R (R ⧸ P) C C M).finrank_eq
    _ = finrank C (C ⊗[S] (S ⊗[R] M)) :=
      (AlgebraTensorModule.cancelBaseChange R S C C M).finrank_eq.symm
    _ = finrank S (S ⊗[R] M) := Module.finrank_baseChange

/-- A finite module over a semilocal ring is free if it becomes free after
an injective integral scalar extension. -/
theorem Module.free_of_free_baseChange_of_integral
    (S : Type*) [CommRing S] [Nontrivial S] [Algebra R S] [FaithfulSMul R S]
    [Algebra.IsIntegral R S] [Finite (MaximalSpectrum R)] [Module.Finite R M]
    [Module.Free S (S ⊗[R] M)] : Module.Free R M := by
  apply Module.free_of_free_baseChange_of_finrank_eq S
  intro P
  exact Module.finrank_residue_eq_of_free_baseChange S P.asIdeal
