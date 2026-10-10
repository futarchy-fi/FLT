/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OpenSectionMonicity
public import FLT.Mazur.LineSectionZeroIdealPullback
public import FLT.Mazur.RelativeSums

/-!
# Assembling regular sections and their flat full zero subschemes

Monicity descends from actual open pullbacks. Once it is constructed, the
full zero ideal commutes with open restriction. Flatness descends through the
induced open cover of the actual zero subscheme, preserving its nilpotents.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Scheme.Modules
namespace FLT.Mazur.SectionCartierOpenDescent
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X S : Scheme.{0}} {ι : Type*}

/-- Monicity of the original section is detected by an open cover of actual pullbacks. -/
theorem mono_of_cover (M : X.Modules) (s : Γ(M, ⊤)) (U : ι → X.Opens)
    (hU : iSup U = ⊤)
    (hs : ∀ i, Mono (globalSectionHom _ (pullGlobal (U i).ι M s))) :
    Mono (globalSectionHom M s) := by
  have hm (i : ι) : Mono ((restrictFunctor (U i).ι).map (globalSectionHom M s)) := by
    have hp := hs i
    rw [globalSectionHom_pullGlobal] at hp
    have := (mono_comp_iff_of_isIso _ _).mp hp
    exact mono_of_mono_fac
      ((restrictFunctorIsoPullback (U i).ι).hom.naturality (globalSectionHom M s))
  refine ⟨fun {N} a b hab ↦ ?_⟩
  apply ModuleSheafMorphismGluing.hom_ext_restrict U hU
  intro i
  have := hm i
  apply (cancel_mono ((restrictFunctor (U i).ι).map (globalSectionHom M s))).mp
  rw [← Functor.map_comp, ← Functor.map_comp, hab]

/-- Flatness of a full subscheme descends from its ideal-sheaf comaps on an open cover. -/
theorem flat_of_comap_cover (f : X ⟶ S) (I : X.IdealSheafData) (C : X.OpenCover)
    (h : ∀ i, Flat ((I.comap (C.f i)).subschemeι ≫ C.f i ≫ f)) :
    Flat (I.subschemeι ≫ f) := by
  apply (IsZariskiLocalAtSource.iff_of_openCover (C.pullback₂ I.subschemeι)).mpr
  intro i
  have := h i
  change Flat (pullback.snd (C.f i) I.subschemeι ≫ I.subschemeι ≫ f)
  have he : pullback.snd (C.f i) I.subschemeι ≫ I.subschemeι ≫ f =
      (I.comapIso (C.f i)).inv ≫ ((I.comap (C.f i)).subschemeι ≫ C.f i ≫ f) := by
    rw [← Category.assoc, ← Category.assoc, I.comapIso_inv_subschemeι,
      pullback.condition_assoc, Category.assoc]
  rw [he]
  infer_instance

/-- Local section embeddings and their full relative Cartier ideals assemble globally. -/
theorem relativeCartier_of_cover (f : X ⟶ S) {M : X.Modules}
    (hM : LocallyFreeRankOne M) (s : Γ(M, ⊤)) (U : ι → X.Opens) (hU : iSup U = ⊤)
    (hs : ∀ i, Mono (globalSectionHom _ (pullGlobal (U i).ι M s)) ∧
      RelativeEffectiveCartier ((U i).ι ≫ f)
        (lineSectionZeroIdeal (hM.pullback (U i).ι) (pullGlobal (U i).ι M s))) :
    Mono (globalSectionHom M s) ∧ RelativeEffectiveCartier f (lineSectionZeroIdeal hM s) := by
  have hm := mono_of_cover M s U hU (fun i ↦ (hs i).1)
  have hI := lineSectionZeroIdeal_effectiveCartier hM s
  refine ⟨hm, hI, ?_⟩
  apply flat_of_comap_cover f _ (X.openCoverOfIsOpenCover U hU)
  intro i
  have hJ := hI.comap_of_isOpenImmersion (U i).ι
  have hi := (hs i).2.2
  rw [lineSectionZeroIdeal_pullGlobal (U i).ι hM s hJ] at hi
  exact hi

end FLT.Mazur.SectionCartierOpenDescent
