/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineModuleExact
public import FLT.Mazur.ModuleSheafOpenIsoDetection

/-!
# Checking short exactness on a scheme open cover

Restrictions preserve kernels, cokernels and homology. The vanishing of these
objects is local, which detects all three conditions of short exactness.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Scheme.Modules ZeroObject
@[expose] public noncomputable section
universe u v
namespace FLT.Mazur.ModuleExactOpenCover
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open FCurve.ModuleSheafOpenIsoDetection
variable {X : Scheme.{u}} {ι : Type v} (U : ι → X.Opens)
  (hU : ∀ x : X, ∃ i, x ∈ U i)
include hU
theorem isZero_of_cover (M : X.Modules)
    (h : ∀ i, IsZero (M.restrict (U i).ι)) : IsZero M := by
  have hz : IsIso (0 : M ⟶ 0) := isIso_of_openCover _ U hU (fun i ↦
    (h i).isIso ((restrictFunctor (U i).ι).map_isZero (isZero_zero X.Modules)) _)
  exact (isZero_zero X.Modules).of_iso (asIso (0 : M ⟶ 0))
theorem exact_of_cover (S : ShortComplex X.Modules)
    (h : ∀ i, (S.map (restrictFunctor (U i).ι)).Exact) : S.Exact := by
  rw [S.exact_iff_isZero_homology]
  apply isZero_of_cover U hU
  intro i
  exact ((S.map (restrictFunctor (U i).ι)).exact_iff_isZero_homology.mp (h i)).of_iso
    (S.mapHomologyIso (restrictFunctor (U i).ι)).symm
theorem mono_of_cover {M N : X.Modules} (f : M ⟶ N)
    (h : ∀ i, Mono ((restrictFunctor (U i).ι).map f)) : Mono f := by
  have hz : IsZero (kernel f) := by
    apply isZero_of_cover U hU
    intro i
    let := h i
    exact (isZero_kernel_of_mono ((restrictFunctor (U i).ι).map f)).of_iso
      (PreservesKernel.iso (restrictFunctor (U i).ι) f)
  exact Abelian.mono_of_kernel_ι_eq_zero _ (hz.eq_of_src _ _)
theorem epi_of_cover {M N : X.Modules} (f : M ⟶ N)
    (h : ∀ i, Epi ((restrictFunctor (U i).ι).map f)) : Epi f := by
  have hz : IsZero (cokernel f) := by
    apply isZero_of_cover U hU
    intro i
    let := h i
    exact (isZero_cokernel_of_epi ((restrictFunctor (U i).ι).map f)).of_iso
      (PreservesCokernel.iso (restrictFunctor (U i).ι) f)
  exact Abelian.epi_of_cokernel_π_eq_zero _ (hz.eq_of_tgt _ _)
theorem shortExact_of_cover (S : ShortComplex X.Modules)
    (h : ∀ i, (S.map (restrictFunctor (U i).ι)).ShortExact) : S.ShortExact :=
  ShortComplex.ShortExact.mk' (exact_of_cover U hU S (fun i ↦ (h i).exact))
    (mono_of_cover U hU S.f (fun i ↦ (h i).mono_f))
    (epi_of_cover U hU S.g (fun i ↦ (h i).epi_g))
omit hU in
/-- Short exactness can be checked on the actual maps of a scheme open cover. -/
theorem shortExact_of_schemeCover (S : ShortComplex X.Modules) (C : X.OpenCover)
    (h : ∀ i, (S.map (restrictFunctor (C.f i))).ShortExact) : S.ShortExact := by
  apply shortExact_of_cover (fun i ↦ (C.f i).opensRange)
    (fun x ↦ by
      obtain ⟨i, y, hy⟩ := C.exists_eq x
      exact ⟨i, y, hy⟩)
  intro i
  let e := (C.f i).isoOpensRange
  let α := (restrictFunctorComp e.inv (C.f i)).symm ≪≫
    restrictFunctorCongr (C.f i).isoOpensRange_inv_comp
  exact ShortComplex.shortExact_of_iso (S.mapNatIso α)
    ((h i).map_of_exact (restrictFunctor e.inv))
end FLT.Mazur.ModuleExactOpenCover
