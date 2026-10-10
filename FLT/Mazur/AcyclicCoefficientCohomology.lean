/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AcyclicTensorExactness
public import FLT.Mazur.AcyclicLineSectionBaseChange

/-!
# Positive cohomology vanishing after arbitrary affine base change

A bounded flat Cech complex that is acyclic in positive degrees remains so
under arbitrary coefficients. Actual cartesian term comparisons transfer the
result to the pulled-back sheaf, without a flatness hypothesis on the new base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules hiding map_smul
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.IncreasingCechCoefficients
open IncreasingCechScalars FCurve Chow

variable {P X T S : Scheme.{0}} [IsAffine T] [IsAffine S] [X.IsSeparated]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  (h : IsPullback p q f g) (M : X.Modules) [M.IsQuasicoherent]
  {ι : Type} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hCover : iSup U = ⊤)
  [∀ n, Module.Flat Γ(S, ⊤) (BaseTerm M U f.appTop.hom n)]
  (hV : ∀ n, Subsingleton (ModuleH M (n + 1)))

omit [IsAffine S] [Finite ι]
  [∀ n, Module.Flat Γ(S, ⊤) (BaseTerm M U f.appTop.hom n)] in
include hU hCover hV in
/-- Acyclicity of actual sheaf cohomology makes every adjacent positive complex exact. -/
theorem acyclic_positiveModuleComplex_exact (n : ℕ) :
    (positiveModuleComplex M U f.appTop.hom n).Exact := by
  let _ : Subsingleton (ModuleRingH f.appTop.hom M (n + 1)) := hV n
  let _ : Subsingleton (BaseHomology M U f.appTop.hom (n + 1)) :=
    (affineRingCohomologyEquiv M U hU hCover f.appTop.hom (n + 1)).injective.subsingleton
  let _ := (positiveModuleHomologyEquiv M U f.appTop.hom n).injective.subsingleton
  exact (ShortComplex.exact_iff_isZero_homology _).mpr (ModuleCat.isZero_of_subsingleton _)

include h hU hCover hV in
/-- Positive acyclicity survives arbitrary affine coefficient extension. -/
theorem acyclic_baseChange_positive (n : ℕ) :
    Subsingleton (ModuleH ((pullback p).obj M) (n + 1)) := by
  let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  have hH := baseHomology_flat_of_ringH M U hU hCover
    (LineSectionBaseChange.positive_flat_of_vanishing f M hV)
  let _ := baseD_cokernel_flat M U f.appTop.hom hH (n + 1)
  have he := acyclic_positiveModuleComplex_exact (f := f) M U hU hCover hV n
  have hex : Function.Exact (baseD M U f.appTop.hom n)
      (baseD M U f.appTop.hom (n + 1)) :=
    LinearMap.exact_iff.mpr he.moduleCat_range_eq_ker.symm
  have ht := TensorKernelFlatCokernel.lTensor_exact_of_cokernel_flat
    (baseD M U f.appTop.hom n) (baseD M U f.appTop.hom (n + 1)) hex Γ(T, ⊤)
  have hm : ((positiveModuleComplex M U f.appTop.hom n).map
      (ModuleCat.extendScalars g.appTop.hom)).Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    exact (ht x).mp hx
  have hp := ShortComplex.exact_of_iso (geometricPositiveComplexIso h M U hU n) hm
  let _ := ModuleCat.subsingleton_of_isZero
    ((ShortComplex.exact_iff_isZero_homology _).mp hp)
  let _ := (positiveModuleHomologyEquiv ((pullback p).obj M)
    (fun i ↦ p ⁻¹ᵁ U i) q.appTop.hom n).symm.injective.subsingleton
  let _ : IsAffineHom p := MorphismProperty.of_isPullback h.flip inferInstance
  let _ : P.IsSeparated := ⟨by
    simpa only [Limits.terminal.comp_from] using
      (inferInstance : IsSeparated (p ≫ Limits.terminal.from X))⟩
  let _ := QuasiCoherentSchemePullback.isQuasicoherent p M
  let e : BaseHomology ((pullback p).obj M) (fun i ↦ p ⁻¹ᵁ U i) q.appTop.hom (n + 1) ≃ₗ[Γ(T, ⊤)]
      ModuleRingH q.appTop.hom ((pullback p).obj M) (n + 1) :=
    affineRingCohomologyEquiv ((pullback p).obj M) (fun i ↦ p ⁻¹ᵁ U i)
      (fun i ↦ (hU i).preimage p) (p.iSup_preimage_eq_top hCover) q.appTop.hom (n + 1)
  exact e.symm.injective.subsingleton

end FLT.Mazur.IncreasingCechCoefficients

namespace FLT.Mazur.LineSectionBaseChange
open FCurve IncreasingCechCoefficients

variable {P X T S : Scheme.{0}} [IsAffine T] [IsAffine S]
  [AlgebraicGeometry.IsNoetherian X] [X.IsSeparated]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S} [Flat f]
  (h : IsPullback p q f g) (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ n, Subsingleton (ModuleH L (n + 1)))

include h hL hV in
/-- An acyclic line in a flat family remains positive-acyclic on every affine base change. -/
theorem acyclic_pullback_positive (n : ℕ) :
    Subsingleton (ModuleH ((pullback p).obj L) (n + 1)) := by
  let _ := hL.isFinitePresentation
  obtain ⟨ι, hι, U, hU⟩ := IdealPowerExtensionCharts.exists_finite_affine_cover (X := X)
  let _ : Finite ι := hι
  let _ := Fintype.ofFinite ι
  let _ := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  let _ (k : ℕ) := FlatLineSectionTerms.term_flat f L hL
    (fun i ↦ (U i).1) (fun i ↦ (U i).2) k
  exact acyclic_baseChange_positive h L (fun i ↦ (U i).1) (fun i ↦ (U i).2) hU hV n

end FLT.Mazur.LineSectionBaseChange
