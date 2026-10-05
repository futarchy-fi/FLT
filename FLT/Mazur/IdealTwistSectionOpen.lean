/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GlobalIdealPower
public import FLT.Mazur.ModuleLineTensorExact
public import FLT.Mazur.ModuleHomIsomorphismOpen

/-!
# Generator opens of ideal-twisted sections

A section coming from an ideal multiple cannot generate over the zero locus
of that ideal. Tensoring the ideal inclusion with a line is injective, so
nonzero ideal-twisted sections give nonzero sections with this open bound.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace FLT.Mazur.FCurve

open FLT.Mazur.GlobalIdealPower ModuleSheafTensor ModuleSheafOpenIsoDetection

variable {X : Scheme} [IsLocallyNoetherian X]

/-- A section in an ideal multiple only generates off the ideal's zero locus. -/
theorem multiple_section_generatorOpen_le (I : X.IdealSheafData)
    (L : X.Modules) [L.IsFinitePresentation] (t : Γ(multiple I L, ⊤)) :
    sectionGeneratorOpen L ((inclusion I L).app ⊤ t) ≤ I.support.compl := by
  let s := (inclusion I L).app ⊤ t
  intro x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    hx (sectionGeneratorOpen L s).isOpen
  let U : X.affineOpens := ⟨V, hV⟩
  have : IsIso ((restrictFunctor (sectionGeneratorOpen L s).ι).map
      (globalSectionHom L s)) := inferInstanceAs
    (IsIso ((restrictFunctor (moduleHomIsoOpen (globalSectionHom L s)).ι).map
      (globalSectionHom L s)))
  have hi : IsIso ((globalSectionHom L s).app V) :=
    isIso_app_of_restrict (globalSectionHom L s) (sectionGeneratorOpen L s) V hVW
  have : IsIso ((globalSectionHom L s).val.app (op V)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (ConcreteCategory.bijective_of_isIso ((globalSectionHom L s).app V))
  let e : Γ(L, V) ≃ₗ[Γ(X, V)] Γ(X, V) :=
    (asIso ((globalSectionHom L s).val.app (op V))).toLinearEquiv.symm
  let tV := (multiple I L).presheaf.map V.leTop.op t
  have hm : (inclusion I L).app V tV ∈ I.ideal U • (⊤ : Submodule Γ(X, V) Γ(L, V)) := by
    rw [← inclusion_range I L U]
    exact ⟨tV, rfl⟩
  have he : ∀ m ∈ I.ideal U • (⊤ : Submodule Γ(X, V) Γ(L, V)), e m ∈ I.ideal U := by
    intro m hm
    exact Submodule.smul_induction_on hm
      (fun r hr m _ ↦ by
        rw [e.map_smul]
        exact (I.ideal U).mul_mem_right (e m) hr)
      (fun a b ha hb ↦ by simpa only [map_add] using (I.ideal U).add_mem ha hb)
  have hs : (inclusion I L).app V tV = (globalSectionHom L s).app V (1 : Γ(X, V)) := by
    have hn := congr($((inclusion I L).val.naturality V.leTop.op) t)
    change (inclusion I L).app V tV = (1 : Γ(X, V)) • L.presheaf.map V.leTop.op s
    rw [one_smul]
    exact hn
  have hone : (1 : Γ(X, V)) ∈ I.ideal U := by
    have h := he _ hm
    rw [hs] at h
    exact (e.apply_symm_apply (1 : Γ(X, V))) ▸ h
  have htop : I.ideal U = ⊤ := Ideal.eq_top_of_isUnit_mem _ hone isUnit_one
  intro hxs
  have hz := (I.mem_support_iff_of_mem (U := U) hxV).mp hxs
  rw [htop] at hz
  change x ∈ X.zeroLocus (U := V) Set.univ at hz
  rw [X.zeroLocus_univ] at hz
  exact hz hxV

omit [IsLocallyNoetherian X] in
/-- The ideal scalar action is the tensor of the actual ideal inclusion followed by the unitor. -/
theorem scalarAction_eq_tensor_inclusion (I : X.IdealSheafData) (L : X.Modules) :
    scalarAction I L = ModuleSheafTensor.map (idealModuleι I) (𝟙 L) ≫ (leftUnitor L).hom := by
  apply ModuleSheafTensor.hom_ext
  intro U a b
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, map_pure, Hom.id_app,
    ConcreteCategory.id_apply, scalarAction_pure]
  exact (leftUnitor_pure L U _ b).symm

omit [IsLocallyNoetherian X] in
/-- Tensoring an ideal inclusion with a line is injective. -/
theorem scalarAction_mono (I : X.IdealSheafData) {L : X.Modules}
    (hL : LocallyFreeRankOne L) : Mono (scalarAction I L) := by
  have h := ModuleLineTensorExact.shortExact (ShortComplex.cokernelSequence (idealModuleι I))
    { exact := ShortComplex.cokernelSequence_exact (idealModuleι I)
      mono_f := inferInstanceAs (Mono (idealModuleι I)) } L hL
  have hm := h.mono_f
  rw [scalarAction_eq_tensor_inclusion]
  exact inferInstanceAs (Mono (((ShortComplex.cokernelSequence (idealModuleι I)).map
    (ModuleSheafTensorCurrying.tensoring L)).f ≫ (leftUnitor L).hom))

/-- An actual ideal-twisted section has generator open in the ideal complement. -/
theorem idealTensor_section_generatorOpen_le (I : X.IdealSheafData)
    (L : X.Modules) [L.IsFinitePresentation] (t : Γ(tensor (idealModule I) L, ⊤)) :
    sectionGeneratorOpen L ((scalarAction I L).app ⊤ t) ≤ I.support.compl := by
  have h := multiple_section_generatorOpen_le I L ((onto I L).app ⊤ t)
  simpa only [← ConcreteCategory.comp_apply, ← Hom.comp_app, onto_inclusion] using h

end FLT.Mazur.FCurve
