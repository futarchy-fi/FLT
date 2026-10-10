/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleFiniteQuotientBranch
public import FLT.Mazur.SmoothFiniteCoefficientBranch
public import FLT.Mazur.CartierFlatNeighborhoodDescent
public import FLT.Mazur.AffineIdealSheafComparison
public import FLT.Mazur.SectionDivisors

/-!
# Cartier descent for flat quasi-finite quotients over arbitrary bases

Every support point has an actual etale ambient neighborhood with finite
flat quotient. Its Cartier equation descends to an open neighborhood of the
original point. This removes the ideal-presentation hypothesis from the
standard-smooth criterion without assuming Noetherian coefficients.
-/

@[expose] public noncomputable section
open TensorProduct CategoryTheory AlgebraicGeometry TopologicalSpace
attribute [local instance] Algebra.TensorProduct.rightAlgebra
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]

/-- Flat quasi-finite presented quotient algebras of smooth curve coordinates are Cartier. -/
theorem effectiveCartier_baseIdeal_of_smooth_quasiFinite_flat
    [Algebra.IsStandardSmoothOfRelativeDimension 1 R B]
    (I : Ideal B) [Algebra.FinitePresentation R (B ⧸ I)]
    [Module.Flat R (B ⧸ I)] [Algebra.QuasiFinite R (B ⧸ I)] :
    EffectiveCartier (BaseAdicThickening.baseIdeal (.of B) I) := by
  rw [effectiveCartier_iff_on_support]
  intro x hx
  let π := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let _ : IsClosedImmersion π :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  rw [← BaseAdicThickening.quotientSpec_ker] at hx
  change x ∈ (π.ker.support : Set _) at hx
  rw [Scheme.Hom.support_ker, π.isClosedMap.isClosed_range.closure_eq] at hx
  obtain ⟨q, hqx⟩ := hx
  obtain ⟨S, hS, hRS, hEt, s, P, hP, hPB, hsP, hfin⟩ :=
    exists_etale_finite_quotient_branch (R := R) I q.asIdeal
  let T := S ⊗[R] B
  let D := Localization.Away s
  let _ := etale_coefficient_branch (R := R) s
  let f := Spec.map (CommRingCat.ofHom (algebraMap B D))
  let _ : Etale f := HasRingHomProperty.Spec_iff.mpr
    (RingHom.etale_algebraMap.mpr inferInstance)
  have hcart : EffectiveCartier ((BaseAdicThickening.baseIdeal (.of B) I).comap f) := by
    rw [BaseAdicThickening.baseIdeal_comap_specMap]
    change EffectiveCartier (BaseAdicThickening.baseIdeal (.of D) (I.map (algebraMap B D)))
    rw [IsScalarTower.algebraMap_eq B T D, ← Ideal.map_map]
    exact effectiveCartier_finite_coefficient_branch (R := R) I s
  apply cartierChart_of_flat_presented_neighborhood _ f hcart x
  have hd : Disjoint (Submonoid.powers s : Set T) (P : Set T) := by
    rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]
  let P' := P.map (algebraMap T D)
  let _ : P'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (.powers s) D P hP hd
  have hPP : P'.comap (algebraMap T D) = P :=
    IsLocalization.under_map_of_isPrime_disjoint (.powers s) D hP hd
  refine ⟨⟨P', inferInstance⟩, ?_⟩
  calc
    f ⟨P', inferInstance⟩ = π q := by
      apply PrimeSpectrum.ext
      change P'.comap (algebraMap B D) = q.asIdeal.comap (Ideal.Quotient.mk I)
      rw [IsScalarTower.algebraMap_eq B T D, ← Ideal.comap_comap, hPP]
      exact hPB
    _ = x := hqx

end FLT.Mazur.FCurve
