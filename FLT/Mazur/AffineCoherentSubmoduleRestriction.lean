/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSubobjectCoverEquality
public import FLT.Mazur.PrincipalSubmoduleOverlap

/-!
# Extending a coherent subsheaf from a quasi-compact affine open

A finite principal cover supplies compatible coefficient submodules. Their
contracted intersection defines a coherent subsheaf of the ambient affine sheaf.
Its restriction agrees with the given inclusion as a subobject.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite PrimeSpectrum
open Scheme.Modules

universe u

namespace FLT.Mazur.AffineCoherentSubmoduleRestriction

open PrincipalSubmoduleCoordinates AffineCoherentSubmoduleExtension
open PrincipalSubmoduleOverlap ModuleSubobjectCoverEquality

variable {R : CommRingCat.{u}}

/-- Compactness extracts a finite principal cover, also for the empty open. -/
lemma finitePrincipalCover (U : (Spec R).Opens) (hU : IsCompact (U : Set (Spec R))) :
    ∃ s : Finset R, (⨆ r : s, basicOpen (r : R)) = U := by
  obtain ⟨s, hs, he⟩ := (Opens.IsBasis.isCompact_open_iff_eq_finite_iUnion
    basicOpen (isBasis_basic_opens (R := R)) isCompact_basicOpen _).mp ⟨hU, U.isOpen⟩
  refine ⟨hs.toFinset, Opens.ext ?_⟩
  simpa only [Opens.coe_iSup, Set.iUnion_coe_set, Set.iUnion_subtype,
    hs.mem_toFinset] using he.symm

section Coordinates

variable (M : (Spec R).Modules) [M.IsQuasicoherent]

/-- Tilde of the coefficient inclusion followed by the canonical affine counit. -/
def coefficientInclusion (P : Submodule R (moduleSpecΓFunctor.obj M)) :
    tilde (ModuleCat.of R P) ⟶ M :=
  (tilde.functor R).map (ModuleCat.ofHom P.subtype) ≫ M.fromTildeΓ

instance coefficientInclusion_mono (P : Submodule R (moduleSpecΓFunctor.obj M)) :
    Mono (coefficientInclusion M P) := by
  have h : Mono (ModuleCat.ofHom P.subtype) :=
    (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
  have hm : Mono ((tilde.functor R).map (ModuleCat.ofHom P.subtype)) :=
    (tilde.functor R).map_mono _
  exact mono_comp _ _

/-- The inclusion's actual principal section map is the localized coefficient map. -/
lemma coefficientInclusion_coordinates (P : Submodule R (moduleSpecΓFunctor.obj M))
    (r : R) (x : TildePrincipalOpen.sections (ModuleCat.of R P) r) :
    coordinates M r ((coefficientInclusion M P).app (basicOpen r) x) =
      IsLocalizedModule.map (.powers r)
        (LocalizedModule.mkLinearMap (.powers r) P)
        (LocalizedModule.mkLinearMap (.powers r) (moduleSpecΓFunctor.obj M)) P.subtype
        (TildePrincipalOpen.sectionsEquiv (ModuleCat.of R P) r x) := by
  change coordinates M r
    ((modulesSpecToSheaf.map M.fromTildeΓ).hom.app (op (basicOpen r)) _) = _
  rw [coordinates_counit]
  exact TildePrincipalOpen.sectionsEquiv_naturality r (ModuleCat.ofHom P.subtype) x

/-- Restricting the constructed inclusion has precisely the localized coefficient image. -/
lemma coefficientInclusion_sectionSubmodule (P : Submodule R (moduleSpecΓFunctor.obj M))
    (U : (Spec R).Opens) (r : R) (hr : basicOpen r ≤ U) :
    sectionSubmodule ((restrictFunctor U.ι).map (coefficientInclusion M P)) r hr =
      P.localized (.powers r) := by
  let T := tilde (ModuleCat.of R P)
  have he (x : Γ(T, U.ι ''ᵁ (chart U r hr ''ᵁ ⊤))) :
      inclusionSection ((restrictFunctor U.ι).map (coefficientInclusion M P)) r hr x =
        (coefficientInclusion M P).app (basicOpen r)
          (T.presheaf.map (eqToHom (chart_image U r hr).symm).op x) := by
    exact (congr($( (coefficientInclusion M P).mapPresheaf.naturality
      (eqToHom (chart_image U r hr).symm).op ) x)).symm
  have hsur := ConcreteCategory.bijective_of_isIso
    (T.presheaf.map (eqToHom (chart_image U r hr).symm).op)
  have hrange := LinearMap.localized'_range_eq_range_localizedMap
    (Localization.Away r) (.powers r) (LocalizedModule.mkLinearMap (.powers r) P)
    (LocalizedModule.mkLinearMap (.powers r) (moduleSpecΓFunctor.obj M)) P.subtype
  rw [Submodule.range_subtype] at hrange
  change sectionSubmodule _ r hr = P.localized' (Localization.Away r) (.powers r) _
  rw [hrange]
  ext x
  rw [mem_sectionSubmodule_iff_actual]
  simp only [he, coefficientInclusion_coordinates, LinearMap.mem_range,
    LinearMap.extendScalarsOfIsLocalization_apply']
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨_, hy⟩
  · rintro ⟨z, hz⟩
    obtain ⟨y, rfl⟩ := (TildePrincipalOpen.sectionsEquiv (ModuleCat.of R P) r).surjective z
    obtain ⟨w, rfl⟩ := hsur.surjective y
    exact ⟨w, hz⟩

/-- A principal chart image is its inverse image in the open subscheme. -/
lemma chart_open_eq (U : (Spec R).Opens) (r : R) (hr : basicOpen r ≤ U) :
    chart U r hr ''ᵁ ⊤ = U.ι ⁻¹ᵁ basicOpen r := by
  apply (Scheme.Hom.image_injective U.ι)
  change U.ι ''ᵁ (chart U r hr ''ᵁ ⊤) = U.ι ''ᵁ (U.ι ⁻¹ᵁ basicOpen r)
  rw [chart_image, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι, inf_eq_right.mpr hr]

variable {M}

/-- Equality on a principal cover supplies lifts on every open by product refinement. -/
lemma sections_of_principalCover {U : (Spec R).Opens} {L N : U.toScheme.Modules}
    [L.IsQuasicoherent] [N.IsQuasicoherent]
    (a : L ⟶ M.restrict U.ι) (b : N ⟶ M.restrict U.ι) [Mono b]
    {ι : Type u} (d : ι → R) (hd : ∀ k, basicOpen (d k) ≤ U)
    (hcov : (⨆ k, basicOpen (d k)) = U)
    (h : ∀ k, sectionSubmodule a (d k) (hd k) = sectionSubmodule b (d k) (hd k))
    (V : U.toScheme.Opens) (s : Γ(L, V)) : ∃ t, b.app V t = a.app V s := by
  apply sections_of_local a b _ V s
  intro W t x hx
  obtain ⟨r, hr, hxr, hrW⟩ := principal_chart_neighborhood U W x hx
  have hxU : U.ι x ∈ (⨆ k, basicOpen (d k)) := by rw [hcov]; exact x.property
  obtain ⟨k, hk⟩ := Opens.mem_iSup.mp hxU
  let hp := (basicOpen_mul_le_left (d k) r).trans (hd k)
  have hsub : chart U (d k * r) hp ''ᵁ ⊤ ≤ chart U r hr ''ᵁ ⊤ := by
    rw [← Scheme.Hom.image_le_image_iff U.ι, chart_image, chart_image]
    exact basicOpen_mul_le_right _ _
  have he : sectionSubmodule a (d k * r) hp = sectionSubmodule b (d k * r) hp := by
    rw [← contraction_localized a (d k) r (hd k), h k,
      contraction_localized b (d k) r (hd k)]
  refine ⟨_, hsub.trans hrW, ?_, sections_of_coordinates a b _ hp he.le
    (ModuleSheafMorphismGluing.res L (hsub.trans hrW) t)⟩
  rw [chart_open_eq] at hxr ⊢
  change U.ι x ∈ basicOpen (d k * r)
  rw [basicOpen_mul]
  exact ⟨hk, hxr⟩

/-- Matching principal images on a cover identifies the actual restricted subobjects. -/
lemma subobject_eq_of_principalCover {U : (Spec R).Opens} {L N : U.toScheme.Modules}
    [L.IsQuasicoherent] [N.IsQuasicoherent]
    (a : L ⟶ M.restrict U.ι) (b : N ⟶ M.restrict U.ι) [Mono a] [Mono b]
    {ι : Type u} (d : ι → R) (hd : ∀ k, basicOpen (d k) ≤ U)
    (hcov : (⨆ k, basicOpen (d k)) = U)
    (h : ∀ k, sectionSubmodule a (d k) (hd k) = sectionSubmodule b (d k) (hd k)) :
    Subobject.mk a = Subobject.mk b := by
  let hab := sections_of_principalCover a b d hd hcov h
  let hba := sections_of_principalCover b a d hd hcov (fun k ↦ (h k).symm)
  exact le_antisymm (Subobject.mk_le_mk_of_comm (factor a b hab) (factor_comp _ _ _))
    (Subobject.mk_le_mk_of_comm (factor b a hba) (factor_comp _ _ _))

end Coordinates

variable {M : (Spec R).Modules}

/-- Every coherent subsheaf on a quasi-compact open extends inside the given affine sheaf.
The output records equality as subobjects and a comparison commuting with inclusion. -/
theorem exists_coherent_extension [IsNoetherianRing R] [M.IsFinitePresentation]
    (U : (Spec R).Opens) (hU : IsCompact (U : Set (Spec R)))
    (L : U.toScheme.Modules) [L.IsFinitePresentation] (i : L ⟶ M.restrict U.ι) [Mono i] :
    ∃ P : Submodule R (moduleSpecΓFunctor.obj M), Module.Finite R P ∧
      (tilde (ModuleCat.of R P)).IsFinitePresentation ∧
      Subobject.mk ((restrictFunctor U.ι).map (coefficientInclusion M P)) = Subobject.mk i ∧
      ∃ e : (tilde (ModuleCat.of R P)).restrict U.ι ≅ L,
        e.hom ≫ i = (restrictFunctor U.ι).map (coefficientInclusion M P) := by
  obtain ⟨s, hs⟩ := finitePrincipalCover U hU
  let d : s → R := fun r ↦ r.val
  have hd (k : s) : basicOpen (d k) ≤ U :=
    (le_iSup (fun r : s ↦ basicOpen (r : R)) k).trans_eq hs
  have hfinite : Module.Finite R (moduleSpecΓFunctor.obj M) :=
    FCurve.affineCoherent_finite_sections M
  obtain ⟨P, hP, hloc⟩ := exists_finite_compatibleExtension d
    (fun k ↦ sectionSubmodule i (d k) (hd k)) (sectionSubmodule_compatible i d hd)
  have hcoh := FCurve.affineTilde_isFinitePresentation_of_finite (ModuleCat.of R P)
  have hrest := FCurve.CoherentDevissage.coherentPresentation_restrict U.ι
    (tilde (ModuleCat.of R P))
  have heq : Subobject.mk ((restrictFunctor U.ι).map (coefficientInclusion M P)) =
      Subobject.mk i := by
    apply subobject_eq_of_principalCover _ _ d hd hs
    intro k
    rw [coefficientInclusion_sectionSubmodule, hloc]
  refine ⟨P, hP, hcoh, heq, Subobject.isoOfMkEqMk _ _ heq, ?_⟩
  exact Subobject.ofMkLEMk_comp heq.le

end FLT.Mazur.AffineCoherentSubmoduleRestriction
