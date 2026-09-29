/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveTwistCechCohomologySum
public import FLT.Mazur.ProjectiveTwistCechCohomologyContraction

/-!
# Homology of the exponent direct sum

Finite-support cycles and boundaries identify categorical homology of a direct
sum with the direct sum of categorical homologies. Applied to the monomial
coordinates, this transports exponent vanishing to the actual sheaf complex.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

universe u

namespace FLT.Mazur.ProjectiveSpace.TwistCechCohomology

section DirectSumHomology

variable (R : Type u) [CommRing R] {κ : Type u}

/-- Componentwise exactness gives exactness on finite-support families. -/
lemma directSum_exact {A B C : κ → Type u}
    [∀ e, AddCommGroup (A e)] [∀ e, Module R (A e)]
    [∀ e, AddCommGroup (B e)] [∀ e, Module R (B e)]
    [∀ e, AddCommGroup (C e)] [∀ e, Module R (C e)]
    (f : ∀ e, A e →ₗ[R] B e) (g : ∀ e, B e →ₗ[R] C e)
    (h : ∀ e, Function.Exact (f e) (g e)) :
    Function.Exact (DirectSum.lmap f) (DirectSum.lmap g) := by
  rw [LinearMap.exact_iff]
  change LinearMap.ker (DFinsupp.mapRange.linearMap g) =
    LinearMap.range (DFinsupp.mapRange.linearMap f)
  rw [DFinsupp.range_mapRangeLinearMap, DFinsupp.ker_mapRangeLinearMap]
  congr 2
  funext e
  exact LinearMap.exact_iff.mp (h e)

variable (T : κ → ShortComplex (ModuleCat.{u} R))

/-- The direct sum of a family of short complexes of modules. -/
def exponentShortSum : ShortComplex (ModuleCat.{u} R) where
  X₁ := ModuleCat.of R (⨁ e, (T e).X₁)
  X₂ := ModuleCat.of R (⨁ e, (T e).X₂)
  X₃ := ModuleCat.of R (⨁ e, (T e).X₃)
  f := ModuleCat.ofHom (DirectSum.lmap fun e ↦ (T e).f.hom)
  g := ModuleCat.ofHom (DirectSum.lmap fun e ↦ (T e).g.hom)
  zero := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply DFinsupp.ext
    intro e
    exact (T e).moduleCat_zero_apply (x e)

/-- The direct sum of the concrete kernels consists of finite-support cycles. -/
abbrev SumCycles := ⨁ e, LinearMap.ker (T e).g.hom

/-- Inclusion of the finite-support cycles. -/
def sumCyclesι : SumCycles R T →ₗ[R] ⨁ e, (T e).X₂ :=
  DirectSum.lmap fun e ↦ (LinearMap.ker (T e).g.hom).subtype

/-- Boundaries regarded as finite-support cycles. -/
def sumToCycles : (⨁ e, (T e).X₁) →ₗ[R] SumCycles R T :=
  DirectSum.lmap fun e ↦ (T e).moduleCatToCycles

/-- Projection to the direct sum of concrete cycle quotients. -/
def sumCyclesπ : SumCycles R T →ₗ[R] ⨁ e, (T e).moduleCatLeftHomologyData.H :=
  DirectSum.lmap fun e ↦ (LinearMap.range (T e).moduleCatToCycles).mkQ

lemma sumCycles_exact : Function.Exact (sumCyclesι R T) (exponentShortSum R T).g.hom :=
  directSum_exact R _ _ fun e ↦ LinearMap.exact_subtype_ker_map (T e).g.hom

lemma sumCycles_injective : Function.Injective (sumCyclesι R T) :=
  (DFinsupp.mapRange_injective _ (fun _ ↦ map_zero _)).mpr fun _ ↦ Subtype.val_injective

lemma sumCyclesπ_exact : Function.Exact (sumToCycles R T) (sumCyclesπ R T) :=
  directSum_exact R _ _ fun e ↦ LinearMap.exact_map_mkQ_range (T e).moduleCatToCycles

lemma sumCyclesπ_surjective : Function.Surjective (sumCyclesπ R T) :=
  (DFinsupp.mapRange_surjective _ (fun _ ↦ map_zero _)).mpr fun e ↦
    (LinearMap.range (T e).moduleCatToCycles).mkQ_surjective

/-- The cycles inclusion satisfies the categorical kernel universal property. -/
def sumCyclesKernel : IsLimit (KernelFork.ofι (f := (exponentShortSum R T).g)
    (ModuleCat.ofHom (sumCyclesι R T))
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply DFinsupp.ext
      intro e
      exact (x e).property)) :=
  ModuleCat.isLimitKernelFork _ _ (sumCycles_exact R T) (sumCycles_injective R T)

lemma sumCyclesKernel_lift :
    (sumCyclesKernel R T).lift (KernelFork.ofι _ (exponentShortSum R T).zero) =
      ModuleCat.ofHom (sumToCycles R T) := by
  apply Fork.IsLimit.hom_ext (sumCyclesKernel R T)
  calc
    _ = (exponentShortSum R T).f :=
      (sumCyclesKernel R T).fac _ WalkingParallelPair.zero
    _ = _ := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply DFinsupp.ext
      intro e
      rfl

/-- The cycle quotient remains a cokernel for the categorical boundary lift. -/
def sumCyclesCokernel
    (f' : (exponentShortSum R T).X₁ ⟶ ModuleCat.of R (SumCycles R T))
    (hf' : f' = ModuleCat.ofHom (sumToCycles R T))
    (h : f' ≫ ModuleCat.ofHom (sumCyclesπ R T) = 0) :
    IsColimit (CokernelCofork.ofπ (ModuleCat.ofHom (sumCyclesπ R T)) h) := by
  subst f'
  exact ModuleCat.isColimitCokernelCofork (ModuleCat.ofHom (sumToCycles R T))
    (ModuleCat.ofHom (sumCyclesπ R T)) (sumCyclesπ_exact R T) (sumCyclesπ_surjective R T)

/-- Kernel and cokernel universal properties compute the categorical homology. -/
def sumLeftHomologyData : (exponentShortSum R T).LeftHomologyData where
  K := ModuleCat.of R (SumCycles R T)
  H := ModuleCat.of R (⨁ e, (T e).moduleCatLeftHomologyData.H)
  i := ModuleCat.ofHom (sumCyclesι R T)
  π := ModuleCat.ofHom (sumCyclesπ R T)
  wi := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply DFinsupp.ext
    intro e
    exact (x e).property
  hi := sumCyclesKernel R T
  wπ := by
    rw [sumCyclesKernel_lift]
    exact ModuleCat.hom_ext (sumCyclesπ_exact R T).linearMap_comp_eq_zero
  hπ := sumCyclesCokernel R T _ (sumCyclesKernel_lift R T) _

/-- Categorical homology commutes with this direct sum, by cycles and boundaries. -/
def shortSumHomologyIso : (exponentShortSum R T).homology ≅
    ModuleCat.of R (⨁ e, (T e).homology) :=
  (sumLeftHomologyData R T).homologyIso ≪≫
    (DFinsupp.mapRange.linearEquiv fun e ↦
      (T e).moduleCatHomologyIso.symm.toLinearEquiv).toModuleIso

end DirectSumHomology

open TwistGradedCech

variable (R : Type u) [CommRing R] (ι : Type u) (n : ℤ) [Fintype ι]

omit [Fintype ι] in
/-- Every differential of the direct sum is computed componentwise, including zeros. -/
lemma sumComplex_d_apply (p q : ℕ) (x : SumTerm R ι n p) (e : DegreeExponent ι n) :
    DFinsupp.toFun ((sumComplex R ι n).d p q x : SumTerm R ι n q) e =
      (exponentComplex R ι n e.val).d p q (x e) := by
  by_cases h : p + 1 = q
  · subst q
    simp only [sumComplex, exponentComplex, CochainComplex.of_d]
    rfl
  · have hs : ¬ (ComplexShape.up ℕ).Rel p q := h
    rw [(sumComplex R ι n).shape p q hs, (exponentComplex R ι n e.val).shape p q hs]
    rfl

/-- The short complex computing homology is the direct sum of exponent short complexes. -/
def sumShortIso (q : ℕ) : (sumComplex R ι n).sc q ≅
    exponentShortSum R (fun e : DegreeExponent ι n ↦ (exponentComplex R ι n e.val).sc q) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply DFinsupp.ext
    intro e
    exact (sumComplex_d_apply R ι n _ _ x e).symm) (by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply DFinsupp.ext
    intro e
    exact (sumComplex_d_apply R ι n _ _ x e).symm)

/-- Actual categorical homology of the sum is the sum of the exponent homologies. -/
def sumHomologyIso (q : ℕ) : (sumComplex R ι n).homology q ≅
    ModuleCat.of R (⨁ e : DegreeExponent ι n, (exponentComplex R ι n e.val).homology q) :=
  ShortComplex.homologyMapIso (sumShortIso R ι n q) ≪≫
    shortSumHomologyIso R (fun e : DegreeExponent ι n ↦ (exponentComplex R ι n e.val).sc q)

/-- The homology comparison starts with the actual twisting-sheaf complex. -/
def sheafSumHomologyIso (q : ℕ) : (sheafComplex R ι n).homology q ≅
    ModuleCat.of R (⨁ e : DegreeExponent ι n, (exponentComplex R ι n e.val).homology q) :=
  HomologicalComplex.homologyMapIso (sheafSumIso R ι n) q ≪≫ sumHomologyIso R ι n q

omit [Fintype ι] in
/-- Vanishing of every exponent homology implies vanishing for the actual sheaf complex. -/
lemma sheaf_isZero_homology_of_exponents [Finite ι] (q : ℕ)
    (h : ∀ e : DegreeExponent ι n, IsZero ((exponentComplex R ι n e.val).homology q)) :
    IsZero ((sheafComplex R ι n).homology q) := by
  let finiteCharts : Fintype ι := Fintype.ofFinite ι
  have hz : IsZero (ModuleCat.of R
      (⨁ e : DegreeExponent ι n, (exponentComplex R ι n e.val).homology q)) := by
    apply ModuleCat.isZero_iff_subsingleton.mpr
    refine ⟨fun x y ↦ DFinsupp.ext fun e ↦ ?_⟩
    exact (ModuleCat.isZero_iff_subsingleton.mp (h e)).elim _ _
  exact hz.of_iso (sheafSumHomologyIso R ι n q)

/-- Intermediate positive cohomology of the actual twisting-sheaf Cech complex vanishes. -/
lemma sheaf_isZero_homology_intermediate (q : ℕ) (hq : q + 2 < Fintype.card ι) :
    IsZero ((sheafComplex R ι n).homology (q + 1)) :=
  sheaf_isZero_homology_of_exponents R ι n (q + 1) fun e ↦
    exponent_isZero_homology_intermediate R ι n e.val q hq

/-- Above the degree threshold, all positive cohomology of the sheaf complex vanishes. -/
lemma sheaf_isZero_homology_large (hn : -(Fintype.card ι : ℤ) < n) (q : ℕ) :
    IsZero ((sheafComplex R ι n).homology (q + 1)) :=
  sheaf_isZero_homology_of_exponents R ι n (q + 1) fun e ↦
    exponent_isZero_homology_large R ι n e.val e.property hn q

end FLT.Mazur.ProjectiveSpace.TwistCechCohomology
