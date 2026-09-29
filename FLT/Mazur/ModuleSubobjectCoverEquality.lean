/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafMorphismGluing
public import FLT.Mazur.PrincipalSubmoduleCoordinates
public import Mathlib.CategoryTheory.Subobject.Basic

/-!
# Equality of module subsheaves from local section images

Local preimages under a monomorphism agree on overlaps and glue uniquely.
Their uniqueness supplies restriction coherence and linearity, hence an actual
factorization of the inclusion. Applying this in both directions gives equality
of subobjects, including for the principal section coordinates on an affine scheme.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Scheme.Modules FLT.Mazur.ModuleSheafMorphismGluing

universe u v

namespace FLT.Mazur.ModuleSubobjectCoverEquality

variable {X : Scheme.{u}} {L N M : X.Modules} (f : L ⟶ M) (g : N ⟶ M) [Mono g]

/-- A sheaf monomorphism is injective on sections. -/
lemma app_injective (V : X.Opens) : Function.Injective (g.app V) := by
  have hg : Mono g.val := (SheafOfModules.forget X.ringCatSheaf).map_mono g
  exact PresheafOfModules.injective_of_mono g.val (op V)

/-- Naturality in the concrete restriction notation. -/
lemma app_res {V W : X.Opens} (h : V ≤ W) (s : Γ(L, W)) :
    f.app V (res L h s) = res M h (f.app W s) :=
  congr($(f.mapPresheaf.naturality (homOfLE h).op) s)

/-- Local lifts glue because injectivity forces their overlap compatibility. -/
lemma exists_lift_of_cover (V : X.Opens) (s : Γ(M, V)) {ι : Type v}
    (W : ι → X.Opens) (hWV : ∀ i, W i ≤ V) (hW : V ≤ iSup W)
    (hs : ∀ i, ∃ t, g.app (W i) t = res M (hWV i) s) :
    ∃ t, g.app V t = s := by
  choose t ht using hs
  obtain ⟨a, ha, _⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf Ab X) W V
    (fun i ↦ homOfLE (hWV i)) hW t (by
      intro i j
      apply app_injective g (W i ⊓ W j)
      change g.app _ (res N inf_le_left _) = g.app _ (res N inf_le_right _)
      rw [app_res, app_res, ht, ht, res_res, res_res])
  refine ⟨a, ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq'
    (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab X) W V
    (fun i ↦ homOfLE (hWV i)) hW
  intro i
  change res M (hWV i) (g.app V a) = res M (hWV i) s
  rw [← app_res]
  exact (congrArg (g.app (W i)) (ha i)).trans (ht i)

/-- Pointwise local image containment implies containment on every open. -/
lemma sections_of_local
    (h : ∀ (V : X.Opens) (s : Γ(L, V)) (x : X), x ∈ V →
      ∃ (W : X.Opens) (hWV : W ≤ V), x ∈ W ∧
        ∃ t, g.app W t = f.app W (res L hWV s))
    (V : X.Opens) (s : Γ(L, V)) : ∃ t, g.app V t = f.app V s := by
  choose W hWV hx t ht using fun x : V ↦ h V s x x.property
  apply exists_lift_of_cover g V (f.app V s) W hWV
  · intro x hxV
    exact Opens.mem_iSup.mpr ⟨⟨x, hxV⟩, hx ⟨x, hxV⟩⟩
  · intro x
    exact ⟨t x, (ht x).trans (app_res f (hWV x) s)⟩

/-- Pointwise image containment on all opens constructs a sheaf factorization. -/
def factor (h : ∀ (V : X.Opens) (s : Γ(L, V)), ∃ t, g.app V t = f.app V s) : L ⟶ N := by
  let a (V : X.Opens) (s : Γ(L, V)) := (h V s).choose
  have ha (V : X.Opens) (s : Γ(L, V)) : g.app V (a V s) = f.app V s :=
    (h V s).choose_spec
  let b : L.presheaf ⟶ N.presheaf :=
    { app := fun V ↦ AddCommGrpCat.ofHom
        { toFun := a V.unop
          map_zero' := by
            apply app_injective g V.unop
            rw [ha, map_zero, map_zero]
          map_add' := fun s t ↦ by
            apply app_injective g V.unop
            rw [ha, map_add, map_add, ha, ha] }
      naturality := fun V W k ↦ by
        ext s
        apply app_injective g W.unop
        change g.app _ (a _ (res L (leOfHom k.unop) s)) =
          g.app _ (res N (leOfHom k.unop) (a _ s))
        rw [ha, app_res, app_res, ha] }
  exact ⟨PresheafOfModules.homMk b (fun V r s ↦ by
    obtain ⟨V⟩ := V
    change Γ(X, V) at r
    change Γ(L, V) at s
    apply app_injective g V
    change g.app _ (a _ (r • s)) = g.app _ (r • a _ s)
    rw [ha, g.app_smul, ha, f.app_smul])⟩

/-- The constructed factorization commutes with the given inclusions. -/
lemma factor_comp (h : ∀ (V : X.Opens) (s : Γ(L, V)), ∃ t, g.app V t = f.app V s) :
    factor f g h ≫ g = f := by
  apply Scheme.Modules.hom_ext
  intro V
  ext s
  exact (h V s).choose_spec

/-- The chosen section lifts commute with every restriction map. -/
lemma factor_res (h : ∀ (V : X.Opens) (s : Γ(L, V)), ∃ t, g.app V t = f.app V s)
    {V W : X.Opens} (hVW : V ≤ W) (s : Γ(L, W)) :
    (factor f g h).app V (res L hVW s) = res N hVW ((factor f g h).app W s) :=
  app_res (factor f g h) hVW s

/-- Equality of all section images yields equality of the actual subobjects. -/
theorem subobject_eq_of_sections [Mono f]
    (h : ∀ (V : X.Opens) (s : Γ(M, V)),
      (∃ t, f.app V t = s) ↔ ∃ t, g.app V t = s) : Subobject.mk f = Subobject.mk g := by
  apply le_antisymm
  · exact Subobject.mk_le_mk_of_comm
      (factor f g (fun V s ↦ (h V (f.app V s)).mp ⟨s, rfl⟩)) (factor_comp _ _ _)
  · exact Subobject.mk_le_mk_of_comm
      (factor g f (fun V s ↦ (h V (g.app V s)).mpr ⟨s, rfl⟩)) (factor_comp _ _ _)

/-- Restriction of a monomorphism is still a monomorphism. -/
instance restrict_mono (U : X.Opens) : Mono ((restrictFunctor U.ι).map g) := by
  apply (SheafOfModules.forget U.toScheme.ringCatSheaf).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro V
  exact app_injective g (U.ι ''ᵁ V.unop)

/-- A local subobject inequality supplies actual preimages on every subopen. -/
lemma sections_of_restrict_le [Mono f] (U V : X.Opens) (hVU : V ≤ U)
    (h : Subobject.mk ((restrictFunctor U.ι).map f) ≤
      Subobject.mk ((restrictFunctor U.ι).map g)) (s : Γ(L, V)) :
    ∃ t, g.app V t = f.app V s := by
  have he : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hVU]
  have hh (s : Γ(L, U.ι ''ᵁ (U.ι ⁻¹ᵁ V))) :
      ∃ t, g.app _ t = f.app _ s := by
    let a := Subobject.ofMkLEMk _ _ h
    refine ⟨a.app (U.ι ⁻¹ᵁ V) s, ?_⟩
    have ha : a ≫ (restrictFunctor U.ι).map g = (restrictFunctor U.ι).map f :=
      Subobject.ofMkLEMk_comp h
    exact congr($(congrArg
      (fun b : L.restrict U.ι ⟶ M.restrict U.ι ↦ b.app (U.ι ⁻¹ᵁ V)) ha) s)
  exact he ▸ hh <| s

/-- Subobjects that agree on an open cover agree globally. -/
theorem subobject_eq_of_openCover [Mono f] {ι : Type v}
    (U : ι → X.Opens) (hU : iSup U = ⊤)
    (h : ∀ i, Subobject.mk ((restrictFunctor (U i).ι).map f) =
      Subobject.mk ((restrictFunctor (U i).ι).map g)) : Subobject.mk f = Subobject.mk g := by
  have go {A B : X.Modules} (a : A ⟶ M) (b : B ⟶ M) [Mono a] [Mono b]
      (hab : ∀ i, Subobject.mk ((restrictFunctor (U i).ι).map a) ≤
        Subobject.mk ((restrictFunctor (U i).ι).map b)) :
      ∀ (V : X.Opens) (s : Γ(A, V)), ∃ t, b.app V t = a.app V s := by
    apply sections_of_local a b
    intro V s x hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show x ∈ iSup U by rw [hU]; trivial)
    exact ⟨V ⊓ U i, inf_le_left, ⟨hx, hi⟩,
      sections_of_restrict_le a b (U i) _ inf_le_right (hab i) (res A inf_le_left s)⟩
  exact le_antisymm
    (Subobject.mk_le_mk_of_comm (factor f g (go f g (fun i ↦ (h i).le)))
      (factor_comp _ _ _))
    (Subobject.mk_le_mk_of_comm (factor g f (go g f (fun i ↦ (h i).ge)))
      (factor_comp _ _ _))

open PrimeSpectrum PrincipalSubmoduleCoordinates

/-- Coordinate image containment gives preimages for the original inclusion on a chart. -/
lemma sections_of_coordinates {R : CommRingCat.{u}} {M : (Spec R).Modules}
    [M.IsQuasicoherent] {U : (Spec R).Opens} {L N : U.toScheme.Modules}
    (f : L ⟶ M.restrict U.ι) (g : N ⟶ M.restrict U.ι) (r : R) (hr : basicOpen r ≤ U)
    (h : sectionSubmodule f r hr ≤ sectionSubmodule g r hr)
    (s : Γ(L, chart U r hr ''ᵁ ⊤)) :
    ∃ t, g.app (chart U r hr ''ᵁ ⊤) t = f.app (chart U r hr ''ᵁ ⊤) s := by
  have hs := h ((mem_sectionSubmodule_iff_actual f r hr _).mpr ⟨s, rfl⟩)
  obtain ⟨t, ht⟩ := (mem_sectionSubmodule_iff_actual g r hr _).mp hs
  refine ⟨t, ?_⟩
  have he := (coordinates M r).injective ht
  change M.presheaf.map (eqToHom (chart_image U r hr).symm).op (g.app _ t) =
    M.presheaf.map (eqToHom (chart_image U r hr).symm).op (f.app _ s) at he
  exact (ConcreteCategory.bijective_of_isIso
    (M.presheaf.map (eqToHom (chart_image U r hr).symm).op)).injective he

/-- Principal chart images form a basis on every open of an affine scheme. -/
lemma principal_chart_neighborhood {R : CommRingCat.{u}} (U : (Spec R).Opens)
    (V : U.toScheme.Opens) (x : U.toScheme) (hx : x ∈ V) :
    ∃ (r : R) (hr : basicOpen r ≤ U),
      x ∈ chart U r hr ''ᵁ ⊤ ∧ chart U r hr ''ᵁ ⊤ ≤ V := by
  obtain ⟨_, ⟨r, rfl⟩, hxr, hrV⟩ := Opens.isBasis_iff_nbhd.mp
    (isBasis_basic_opens (R := R)) (show U.ι x ∈ U.ι ''ᵁ V from ⟨x, hx, rfl⟩)
  have hr : basicOpen r ≤ U := hrV.trans (by
    simpa only [Scheme.Opens.opensRange_ι] using U.ι.image_le_opensRange V)
  refine ⟨r, hr, ?_, ?_⟩
  · have him : U.ι x ∈ U.ι ''ᵁ (chart U r hr ''ᵁ ⊤) := by
      rw [chart_image]
      exact hxr
    obtain ⟨y, hy, he⟩ := him
    exact (U.ι.isOpenEmbedding.injective he) ▸ hy
  · rw [← Scheme.Hom.image_le_image_iff U.ι, chart_image]
    exact hrV

/-- Principal coordinate containment extends to sections on arbitrary opens. -/
lemma sections_of_principal {R : CommRingCat.{u}} {M : (Spec R).Modules}
    [M.IsQuasicoherent] {U : (Spec R).Opens} {L N : U.toScheme.Modules}
    (f : L ⟶ M.restrict U.ι) (g : N ⟶ M.restrict U.ι) [Mono g]
    (h : ∀ (r : R) (hr : basicOpen r ≤ U),
      sectionSubmodule f r hr ≤ sectionSubmodule g r hr)
    (V : U.toScheme.Opens) (s : Γ(L, V)) : ∃ t, g.app V t = f.app V s := by
  apply sections_of_local f g _ V s
  intro W t x hx
  obtain ⟨r, hr, hxr, hrW⟩ := principal_chart_neighborhood U W x hx
  exact ⟨_, hrW, hxr, sections_of_coordinates f g r hr (h r hr) (res L hrW t)⟩

/-- A factorization of actual inclusions, constructed only from principal section images. -/
def principalFactor {R : CommRingCat.{u}} {M : (Spec R).Modules}
    [M.IsQuasicoherent] {U : (Spec R).Opens} {L N : U.toScheme.Modules}
    (f : L ⟶ M.restrict U.ι) (g : N ⟶ M.restrict U.ι) [Mono g]
    (h : ∀ (r : R) (hr : basicOpen r ≤ U),
      sectionSubmodule f r hr ≤ sectionSubmodule g r hr) : L ⟶ N :=
  factor f g (sections_of_principal f g h)

/-- The principal-basis construction commutes with the original sheaf monomorphism. -/
lemma principalFactor_comp {R : CommRingCat.{u}} {M : (Spec R).Modules}
    [M.IsQuasicoherent] {U : (Spec R).Opens} {L N : U.toScheme.Modules}
    (f : L ⟶ M.restrict U.ι) (g : N ⟶ M.restrict U.ι) [Mono g]
    (h : ∀ (r : R) (hr : basicOpen r ≤ U),
      sectionSubmodule f r hr ≤ sectionSubmodule g r hr) : principalFactor f g h ≫ g = f :=
  factor_comp f g _

/-- Equality on the principal basis identifies the subsheaves as subobjects on the given open. -/
theorem subobject_eq_of_principal_sections {R : CommRingCat.{u}} {M : (Spec R).Modules}
    [M.IsQuasicoherent] {U : (Spec R).Opens} {L N : U.toScheme.Modules}
    (f : L ⟶ M.restrict U.ι) (g : N ⟶ M.restrict U.ι) [Mono f] [Mono g]
    (h : ∀ (r : R) (hr : basicOpen r ≤ U), sectionSubmodule f r hr =
      sectionSubmodule g r hr) : Subobject.mk f = Subobject.mk g :=
  le_antisymm
    (Subobject.mk_le_mk_of_comm (principalFactor f g (fun r hr ↦ (h r hr).le))
      (principalFactor_comp _ _ _))
    (Subobject.mk_le_mk_of_comm (principalFactor g f (fun r hr ↦ (h r hr).ge))
      (principalFactor_comp _ _ _))

end FLT.Mazur.ModuleSubobjectCoverEquality
