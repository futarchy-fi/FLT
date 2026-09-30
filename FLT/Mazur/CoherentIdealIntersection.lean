/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoherentGenericExtension
public import FLT.Mazur.IdealModuleSheaf

/-!
# Intersections of nonzero coherent ideals

The intersection is the infimum of the actual quasi-coherent ideal data. Its
module inclusions give coherent quotient sequences after closed pushforward.
On an integral scheme nonzero ideals have proper zero loci, so the two quotient
supports omit the image of the generic point.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.FCurve.CoherentDevissage
open FLT.Mazur.ModuleSubobjectCoverEquality FLT.Mazur.ModuleSheafMorphismGluing

universe u

namespace FLT.Mazur.CoherentIdealIntersection

variable {X Y : Scheme.{u}}

/-- The structure module is coherent on a locally Noetherian scheme. -/
theorem structureModule_coherent [IsLocallyNoetherian X] :
    (structureModule X).IsFinitePresentation := by
  apply coherentPresentation_of_affine_restrict
  intro U
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have h : (structureModule (Spec Γ(X, U.1))).IsFinitePresentation := by
    exact affineTilde_isFinitePresentation_of_finite (ModuleCat.of Γ(X, U.1) Γ(X, U.1))
  exact (SheafOfModules.isFinitePresentation (Spec Γ(X, U.1)).ringCatSheaf).prop_of_iso
    (restrictUnitIso U.2.fromSpec).symm h

/-- Quasi-coherent ideal data define coherent ideal modules over Noetherian schemes. -/
theorem idealModule_coherent [IsLocallyNoetherian X] (I : X.IdealSheafData) :
    (idealModule I).IsFinitePresentation := by
  have := structureModule_coherent (X := X)
  have := LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
  have := structureModule_coherent (X := I.subscheme)
  have := closedPushforward_isFinitePresentation I.subschemeι (structureModule I.subscheme)
  exact coherent_kernel (idealQuotientMap I)

/-- Ideal containment gives local lifts of the actual ideal module inclusion. -/
lemma ideal_sections_lift {I J : X.IdealSheafData} (h : I ≤ J)
    (V : X.Opens) (s : Γ(idealModule I, V)) :
    ∃ t, (idealModuleι J).app V t = (idealModuleι I).app V s := by
  apply sections_of_local (idealModuleι I) (idealModuleι J) _ V s
  intro W t x hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx W.isOpen
  refine ⟨U, hUW, hxU, ?_⟩
  change (idealModuleι I).app U (res (idealModule I) hUW t) ∈
    Set.range ((idealModuleι J).app U)
  rw [idealModuleι_range J ⟨U, hU⟩]
  apply h ⟨U, hU⟩
  exact (Set.ext_iff.mp (idealModuleι_range I ⟨U, hU⟩) _).mp ⟨_, rfl⟩

/-- The canonical map between the ideal modules of comparable ideal data. -/
def idealMap {I J : X.IdealSheafData} (h : I ≤ J) : idealModule I ⟶ idealModule J :=
  factor (idealModuleι I) (idealModuleι J) (ideal_sections_lift h)

@[simp]
lemma idealMap_comp {I J : X.IdealSheafData} (h : I ≤ J) :
    idealMap h ≫ idealModuleι J = idealModuleι I := factor_comp _ _ _

instance idealMap_mono {I J : X.IdealSheafData} (h : I ≤ J) : Mono (idealMap h) := by
  have : Mono (idealMap h ≫ idealModuleι J) := by rw [idealMap_comp]; infer_instance
  exact mono_of_mono (idealMap h) (idealModuleι J)

/-- The zero locus of an intersection is the union of the two zero loci. -/
lemma intersection_support (I J : X.IdealSheafData) :
    (I ⊓ J).support = I.support ⊔ J.support := by
  rw [← Scheme.IdealSheafData.support_radical (I ⊓ J),
    Scheme.IdealSheafData.radical_inf, ← Scheme.IdealSheafData.radical_mul,
    Scheme.IdealSheafData.support_radical, Scheme.IdealSheafData.support_mul]

/-- A nonzero ideal on an integral scheme does not vanish at the generic point. -/
lemma genericPoint_notMem_zeroLocus [IsIntegral X] (I : X.IdealSheafData) (hI : I ≠ ⊥) :
    genericPoint X ∉ I.support := by
  intro hx
  have hs : (Set.univ : Set X) ⊆ I.support :=
    (genericPoint_spec X) ▸
      closure_minimal (Set.singleton_subset_iff.mpr hx) I.support.isClosed
  have ht : I.support = ⊤ := top_unique hs
  exact hI (Scheme.IdealSheafData.support_eq_top_iff.mp ht)

/-- The intersection of two nonzero quasi-coherent ideals is nonzero. -/
theorem intersection_ne_bot [IsIntegral X] (I J : X.IdealSheafData)
    (hI : I ≠ ⊥) (hJ : J ≠ ⊥) : I ⊓ J ≠ ⊥ := by
  intro h
  have hx : genericPoint X ∈ (I ⊓ J).support := by rw [h]; trivial
  rw [intersection_support] at hx
  exact hx.elim (genericPoint_notMem_zeroLocus I hI) (genericPoint_notMem_zeroLocus J hJ)

/-- Outside its zero locus the ideal inclusion is an isomorphism on stalks. -/
lemma idealModuleι_stalk_isIso (I : X.IdealSheafData) (x : X) (hx : x ∉ I.support) :
    IsIso ((stalk x).map (idealModuleι I)) := by
  have hz := closedPushforward_stalk_isZero I.subschemeι (structureModule I.subscheme) x
    (by rw [I.range_subschemeι]; exact hx)
  have hq : (stalk x).map (idealQuotientMap I) = 0 := hz.eq_of_tgt _ _
  have : IsIso (kernel.ι ((stalk x).map (idealQuotientMap I))) := kernel.ι_of_zero hq
  have he : (stalk x).map (idealModuleι I) =
      (PreservesKernel.iso (stalk x) (idealQuotientMap I)).hom ≫
        kernel.ι ((stalk x).map (idealQuotientMap I)) :=
    (kernelComparison_comp_ι (idealQuotientMap I) (stalk x)).symm
  rw [he]
  infer_instance

/-- Comparable nonzero ideals have the same generic stalk under their actual inclusion. -/
lemma idealMap_generic_isIso [IsIntegral X] {I J : X.IdealSheafData}
    (h : I ≤ J) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    IsIso ((stalk (genericPoint X)).map (idealMap h)) := by
  have := idealModuleι_stalk_isIso I (genericPoint X) (genericPoint_notMem_zeroLocus I hI)
  have := idealModuleι_stalk_isIso J (genericPoint X) (genericPoint_notMem_zeroLocus J hJ)
  have he : (stalk (genericPoint X)).map (idealMap h) ≫
      (stalk (genericPoint X)).map (idealModuleι J) =
        (stalk (genericPoint X)).map (idealModuleι I) := by
    rw [← Functor.map_comp, idealMap_comp]
  have : IsIso ((stalk (genericPoint X)).map (idealMap h) ≫
      (stalk (genericPoint X)).map (idealModuleι J)) := by rw [he]; infer_instance
  exact IsIso.of_isIso_comp_right _ ((stalk (genericPoint X)).map (idealModuleι J))

/-- The closed-pushforward stalk comparison commutes with every module morphism. -/
lemma closed_stalk_naturality (i : X ⟶ Y) [IsClosedImmersion i]
    {L N : X.Modules} (f : L ⟶ N) (x : X) :
    (stalk (i x)).map ((pushforward i).map f) ≫ (closedPushforwardStalkIso i N x).hom =
      (closedPushforwardStalkIso i L x).hom ≫ (stalk x).map f := by
  apply ((pushforward i).obj L).presheaf.stalk_hom_ext
  intro U hx
  change ((i.base _* L.presheaf).germ U (i x) hx) ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat (i x)).map
        ((TopCat.Presheaf.pushforward AddCommGrpCat i.base).map f.mapPresheaf) ≫
          N.presheaf.stalkPushforward AddCommGrpCat i.base x =
    ((i.base _* L.presheaf).germ U (i x) hx) ≫
      L.presheaf.stalkPushforward AddCommGrpCat i.base x ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map f.mapPresheaf
  erw [← Category.assoc, TopCat.Presheaf.stalkFunctor_map_germ, Category.assoc,
    TopCat.Presheaf.stalkPushforward_germ, ← Category.assoc,
    TopCat.Presheaf.stalkPushforward_germ, TopCat.Presheaf.stalkFunctor_map_germ]
  rfl

/-- Closed pushforward preserves a stalk isomorphism at every point in its image. -/
lemma closed_map_stalk_isIso (i : X ⟶ Y) [IsClosedImmersion i]
    {L N : X.Modules} (f : L ⟶ N) (x : X) [IsIso ((stalk x).map f)] :
    IsIso ((stalk (i x)).map ((pushforward i).map f)) := by
  have he := closed_stalk_naturality i f x
  have : IsIso ((stalk (i x)).map ((pushforward i).map f) ≫
      (closedPushforwardStalkIso i N x).hom) := by rw [he]; infer_instance
  exact IsIso.of_isIso_comp_right _ (closedPushforwardStalkIso i N x).hom

/-- Closed pushforward preserves epimorphisms, as detected on and off the closed image. -/
instance closedPushforward_preservesEpis (i : X ⟶ Y) [IsClosedImmersion i] :
    (pushforward i).PreservesEpimorphisms where
  preserves {L N} f _ := by
    let g := (pushforward i).map f
    have hs (y : Y) : Epi ((stalk y).map g) := by
      by_cases hy : y ∈ Set.range i
      · obtain ⟨x, rfl⟩ := hy
        have he : (stalk (i x)).map g = (closedPushforwardStalkIso i L x).hom ≫
            (stalk x).map f ≫ (closedPushforwardStalkIso i N x).inv := by
          apply (cancel_mono (closedPushforwardStalkIso i N x).hom).mp
          simpa using closed_stalk_naturality i f x
        rw [he]
        infer_instance
      · exact epi_of_target_iso_zero _ (closedPushforward_stalk_isZero i N y hy).isoZero
    have hz : IsZero (cokernel g) := (support_eq_empty_iff_isZero _).mp (by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y
      exact (notMem_support_cokernel_iff g y).mpr (hs y))
    exact Abelian.epi_of_cokernel_π_eq_zero g (hz.eq_of_tgt _ _)

instance closedPushforward_preservesHomology (i : X ⟶ Y) [IsClosedImmersion i] :
    (pushforward i).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

instance closedPushforward_finiteColimits (i : X ⟶ Y) [IsClosedImmersion i] :
    PreservesFiniteColimits (pushforward i) :=
  (pushforward i).preservesFiniteColimits_of_preservesHomology

/-- Pushforward of the actual ideal quotient sequence is short exact and coherent. -/
theorem map_ideal_cokernelSequence [IsLocallyNoetherian Y]
    (i : X ⟶ Y) [IsClosedImmersion i] {I J : X.IdealSheafData} (h : I ≤ J) :
    CoherentSequence ((ShortComplex.cokernelSequence (idealMap h)).map (pushforward i)) := by
  have := LocallyOfFiniteType.isLocallyNoetherian i
  have := idealModule_coherent I
  have := idealModule_coherent J
  have := coherent_cokernel (idealMap h)
  exact ⟨(coherent_cokernelSequence (idealMap h)).shortExact.map_of_exact _,
    closedPushforward_isFinitePresentation i (idealModule I),
    closedPushforward_isFinitePresentation i (idealModule J),
    closedPushforward_isFinitePresentation i (cokernel (idealMap h))⟩

/-- The pushforward of the actual quotient has support omitting the generic point. -/
theorem map_ideal_quotient_notMem_generic [IsIntegral X]
    (i : X ⟶ Y) [IsClosedImmersion i] {I J : X.IdealSheafData}
    (h : I ≤ J) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    i (genericPoint X) ∉ support ((pushforward i).obj (cokernel (idealMap h))) := by
  have := idealMap_generic_isIso h hI hJ
  rw [mem_support_closedPushforward]
  exact (notMem_support_cokernel_iff _ _).mpr inferInstance

/-- The actual pushed-forward ideal inclusion. -/
def pushedIdealMap (i : X ⟶ Y) {I J : X.IdealSheafData} (h : I ≤ J) :
    (pushforward i).obj (idealModule I) ⟶ (pushforward i).obj (idealModule J) :=
  (pushforward i).map (idealMap h)

instance pushedIdealMap_mono (i : X ⟶ Y) {I J : X.IdealSheafData} (h : I ≤ J) :
    Mono (pushedIdealMap i h) := by dsimp [pushedIdealMap]; infer_instance

/-- The inclusion and its actual cokernel form a coherent short exact sequence. -/
theorem pushedIdealSequence [IsLocallyNoetherian Y] (i : X ⟶ Y) [IsClosedImmersion i]
    {I J : X.IdealSheafData} (h : I ≤ J) :
    CoherentSequence (ShortComplex.cokernelSequence (pushedIdealMap i h)) := by
  have := LocallyOfFiniteType.isLocallyNoetherian i
  have := idealModule_coherent I
  have := idealModule_coherent J
  have := closedPushforward_isFinitePresentation i (idealModule I)
  have := closedPushforward_isFinitePresentation i (idealModule J)
  exact coherent_cokernelSequence _

/-- The pushed quotient of comparable nonzero ideals omits the generic point. -/
theorem pushed_quotient_notMem_generic [IsIntegral X]
    (i : X ⟶ Y) [IsClosedImmersion i] {I J : X.IdealSheafData}
    (h : I ≤ J) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    i (genericPoint X) ∉ support (cokernel (pushedIdealMap i h)) := by
  have := idealMap_generic_isIso h hI hJ
  have : IsIso ((stalk (i (genericPoint X))).map (pushedIdealMap i h)) :=
    closed_map_stalk_isIso i (idealMap h) (genericPoint X)
  exact (notMem_support_cokernel_iff _ _).mpr inferInstance

/-- These quotient supports are strictly smaller than the integral closed image. -/
theorem pushed_quotient_support_ssubset [IsIntegral X]
    (i : X ⟶ Y) [IsClosedImmersion i] {I J : X.IdealSheafData}
    (h : I ≤ J) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    support (cokernel (pushedIdealMap i h)) ⊂ Set.range i := by
  refine ⟨(support_subset_of_epi (cokernel.π (pushedIdealMap i h))).trans
    (support_closedPushforward_subset_range i (idealModule J)), ?_⟩
  intro he
  exact pushed_quotient_notMem_generic i h hI hJ (he ⟨genericPoint X, rfl⟩)

/-- The constructed intersection gives both required coherent sequences and support bounds. -/
theorem intersection_sequences [IsIntegral X] [IsLocallyNoetherian Y]
    (i : X ⟶ Y) [IsClosedImmersion i] (I J : X.IdealSheafData)
    (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    I ⊓ J ≠ ⊥ ∧
      CoherentSequence (ShortComplex.cokernelSequence
        (pushedIdealMap i (inf_le_left : I ⊓ J ≤ I))) ∧
      CoherentSequence (ShortComplex.cokernelSequence
        (pushedIdealMap i (inf_le_right : I ⊓ J ≤ J))) ∧
      support (cokernel (pushedIdealMap i (inf_le_left : I ⊓ J ≤ I))) ⊂ Set.range i ∧
      support (cokernel (pushedIdealMap i (inf_le_right : I ⊓ J ≤ J))) ⊂ Set.range i := by
  have hIJ := intersection_ne_bot I J hI hJ
  exact ⟨hIJ, pushedIdealSequence i _, pushedIdealSequence i _,
    pushed_quotient_support_ssubset i _ hIJ hI,
    pushed_quotient_support_ssubset i _ hIJ hJ⟩

/-- Both short exact sequences are pushforwards of the constructed intersection quotients. -/
theorem intersection_pushforward_sequences [IsIntegral X] [IsLocallyNoetherian Y]
    (i : X ⟶ Y) [IsClosedImmersion i] (I J : X.IdealSheafData)
    (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    I ⊓ J ≠ ⊥ ∧
      CoherentSequence ((ShortComplex.cokernelSequence
        (idealMap (inf_le_left : I ⊓ J ≤ I))).map (pushforward i)) ∧
      CoherentSequence ((ShortComplex.cokernelSequence
        (idealMap (inf_le_right : I ⊓ J ≤ J))).map (pushforward i)) ∧
      i (genericPoint X) ∉ support ((pushforward i).obj
        (cokernel (idealMap (inf_le_left : I ⊓ J ≤ I)))) ∧
      i (genericPoint X) ∉ support ((pushforward i).obj
        (cokernel (idealMap (inf_le_right : I ⊓ J ≤ J)))) := by
  have hIJ := intersection_ne_bot I J hI hJ
  exact ⟨hIJ, map_ideal_cokernelSequence i _, map_ideal_cokernelSequence i _,
    map_ideal_quotient_notMem_generic i _ hIJ hI,
    map_ideal_quotient_notMem_generic i _ hIJ hJ⟩

end FLT.Mazur.CoherentIdealIntersection
