/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.Localization.Finiteness

/-!
# Finite modules and affine module sheaves

A locally finitely presented module sheaf on an affine scheme has finite global
sections. For quasi-coherent sheaves over a Noetherian ring, the converse holds:
these are exactly the sheaves associated to finite modules. The comparisons use
Mathlib's `fromTildeΓ` counit,
`tildeEquiv`, and the canonical linear equivalence on global sections.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry

universe u v w v₂ w₂

namespace FLT.Mazur.FCurve

section Presentation

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {D : Type v₂} [Category.{w₂} D] {K : GrothendieckTopology D}
  {S : Sheaf K RingCat.{u}} [HasSheafify K AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A functor preserving colimits and the unit preserves finite presentations. -/
lemma affinePresentation_map_isFinite {M : SheafOfModules.{u} R}
    (P : M.Presentation) [P.IsFinite]
    (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S)
    [PreservesColimitsOfSize.{u, u} F] (e : SheafOfModules.unit S ≅ F.obj (.unit R)) :
    (P.map F e).IsFinite where
  isFiniteType_generators := ⟨by simpa using inferInstanceAs (Finite P.generators.I)⟩
  isFiniteType_relations := ⟨by simpa using inferInstanceAs (Finite P.relations.I)⟩

/-- A finite global presentation yields Mathlib's local finite presentation. -/
lemma affinePresentation_isFinitePresentation [HasBinaryProducts C]
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M : SheafOfModules.{u} R} (P : M.Presentation) [P.IsFinite] :
    M.IsFinitePresentation := by
  refine ⟨P.quasicoherentData, ⟨fun X ↦ ?_⟩⟩
  change C at X
  exact affinePresentation_map_isFinite P
    (SheafOfModules.pushforward (F := Over.forget X) (𝟙 (R.over X)))
    (Iso.refl _)

/-- Finite generating families transport across an isomorphism. -/
lemma affineGenerators_exists_of_iso {M N : SheafOfModules.{u} R} (e : M ≅ N)
    (G : M.GeneratingSections) [G.IsFiniteType] :
    ∃ H : N.GeneratingSections, H.IsFiniteType :=
  ⟨G.ofEpi e.hom, inferInstance⟩

end Presentation

variable {R : CommRingCat.{u}}

/-- A finite family generating a quasi-coherent affine sheaf generates a finite
module of global sections. -/
theorem affineSections_finite_of_generators (M : (Spec R).Modules) [M.IsQuasicoherent]
    (G : M.GeneratingSections) [G.IsFiniteType] : Module.Finite R Γ(M, ⊤) := by
  let f : tilde (ModuleCat.of R (G.I →₀ R)) ⟶ tilde (moduleSpecΓFunctor.obj M) :=
    (tildeFinsupp G.I).hom ≫ G.π ≫ inv M.fromTildeΓ
  have : Epi G.π := G.epi
  have : Epi f := by dsimp [f]; infer_instance
  let g : ModuleCat.of R (G.I →₀ R) ⟶ moduleSpecΓFunctor.obj M :=
    (tilde.functor R).preimage f
  have : Epi ((tilde.functor R).map g) := by
    change Epi ((tilde.functor R).map ((tilde.functor R).preimage f))
    rw [Functor.map_preimage]
    infer_instance
  have : Epi g := (tilde.functor R).epi_of_epi_map inferInstance
  exact Module.Finite.of_surjective g.hom ((ModuleCat.epi_iff_surjective g).mp inferInstance)

/-- A finite global presentation on an affine scheme gives finite global sections. -/
theorem affineSections_finite_of_presentation (M : (Spec R).Modules)
    (P : M.Presentation) [P.IsFinite] : Module.Finite R Γ(M, ⊤) := by
  have := P.isQuasicoherent
  exact affineSections_finite_of_generators M P.generators

open Scheme.Modules in
/-- Finite generators on the over site give finite generators on the open subscheme. -/
lemma affineGenerators_over_exists {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (G : (M.over U).GeneratingSections) [G.IsFiniteType] :
    ∃ H : (M.restrict U.ι).GeneratingSections, H.IsFiniteType := by
  let F := (overEquiv U).functor
  let e : SheafOfModules.unit _ ≅ F.obj (.unit _) := Iso.refl _
  let eM : F.obj (M.over U) ≅ M.restrict U.ι := (overFunctorEquiv U).app M
  exact affineGenerators_exists_of_iso.{u, u, u} eM (G.map F e)

open TopologicalSpace PrimeSpectrum in
/-- Refine a cover of an affine spectrum by all principal opens contained in its members. -/
lemma affinePrincipalCover_sup {ι : Type u} (U : ι → (Spec R).Opens)
    (hU : (⨆ i, U i) = ⊤) :
    (⨆ i : Σ j, {r : R // basicOpen r ≤ U j}, basicOpen i.2.1) = ⊤ := by
  apply top_unique
  intro x _
  have hx : x ∈ ⨆ i, U i := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  obtain ⟨_, ⟨r, rfl⟩, hr, hsub⟩ :=
    Opens.isBasis_iff_nbhd.mp (PrimeSpectrum.isBasis_basic_opens (R := R)) hi
  exact Opens.mem_iSup.mpr ⟨⟨i, r, hsub⟩, hr⟩

open PrimeSpectrum Scheme.Modules in
/-- Finite generators on an open restrict to finite generators on a contained principal open. -/
lemma affineGenerators_basicOpen_exists (M : (Spec R).Modules) (U : (Spec R).Opens)
    (r : R) (hr : basicOpen r ≤ U) (G : (M.over U).GeneratingSections) [G.IsFiniteType] :
    ∃ H : (M.restrict (Spec.map (CommRingCat.ofHom
      (algebraMap R (Localization.Away r))))).GeneratingSections, H.IsFiniteType := by
  let t := (Spec R).homOfLE (U := basicOpen r) (V := U) hr
  let f := (basicOpenIsoSpecAway r).inv ≫ t
  obtain ⟨G', hG'⟩ := affineGenerators_over_exists M U G
  have := hG'
  have : PreservesColimitsOfSize.{u, u} (restrictFunctor.{u} f) := inferInstance
  let H := G'.map (restrictFunctor.{u} f) (restrictUnitIso f).symm
  let iso : restrictFunctor U.ι ⋙ restrictFunctor f ≅
      restrictFunctor (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) :=
    (restrictFunctorComp f U.ι).symm ≪≫
      restrictFunctorCongr (by
        simp only [f, t, Category.assoc, Scheme.homOfLE_ι]
        rw [← basicOpenIsoSpecAway_hom_SpecMap r, Iso.inv_hom_id_assoc])
  exact affineGenerators_exists_of_iso.{u, u, u} (iso.app M) H

open TopologicalSpace PrimeSpectrum Scheme.Modules in
/-- Local finite presentations yield finite generators on a principal affine cover. -/
lemma affineCoherent_principalCover (M : (Spec R).Modules) [M.IsFinitePresentation] :
    ∃ (ι : Type u) (a : ι → R), (⨆ i, basicOpen (a i)) = ⊤ ∧
      ∀ i, ∃ G : (M.restrict (Spec.map (CommRingCat.ofHom
        (algebraMap R (Localization.Away (a i)))))).GeneratingSections, G.IsFiniteType := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  let := hq
  let ι := Σ i : q.I, {r : R // basicOpen r ≤ q.X i}
  refine ⟨ι, fun i ↦ i.2.1, ?_, ?_⟩
  · have cov := q.coversTop
    rw [Opens.coversTop_iff, IsOpenCover] at cov
    exact affinePrincipalCover_sup q.X cov
  · rintro ⟨j, r, hr⟩
    have : (q.presentation j).IsFinite := hq.isFinite_presentation j
    exact affineGenerators_basicOpen_exists M (q.X j) r hr (q.presentation j).generators

/-- Finite sections on an affine restriction remain finite over the ring of
functions on its image, with the scalar action supplied by the open immersion. -/
lemma affineSections_finite_on_image {X : Scheme.{u}} {S : CommRingCat.{u}}
    (M : X.Modules) [M.IsQuasicoherent] (f : Spec S ⟶ X) [IsOpenImmersion f]
    (G : (M.restrict f).GeneratingSections) [G.IsFiniteType] :
    Module.Finite Γ(X, f ''ᵁ ⊤) Γ(M, f ''ᵁ ⊤) := by
  have := affineSections_finite_of_generators (M.restrict f) G
  have := Module.Finite.of_restrictScalars_finite S Γ(Spec S, ⊤) Γ(M.restrict f, ⊤)
  let g : Γ(M.restrict f, ⊤) →ₛₗ[(f.appIso ⊤).inv.hom] Γ(M, f ''ᵁ ⊤) :=
    { toFun := (M.restrictAppIso f ⊤).hom
      map_add' := map_add _
      map_smul' := fun r x ↦ M.smul_restrictAppIso_hom_apply f ⊤ r x }
  exact Module.Finite.of_surjective g
    ((ConcreteCategory.bijective_of_isIso (M.restrictAppIso f ⊤).hom).surjective)

open PrimeSpectrum in
/-- A locally finitely presented sheaf on an affine scheme has finite global sections. -/
theorem affineCoherent_finite_sections (M : (Spec R).Modules) [M.IsFinitePresentation] :
    Module.Finite R Γ(M, ⊤) := by
  obtain ⟨ι, a, ha, hG⟩ := affineCoherent_principalCover M
  have hfin (i : ι) : Module.Finite Γ(Spec R, basicOpen (a i)) Γ(M, basicOpen (a i)) := by
    obtain ⟨G, hG⟩ := hG i
    let := hG
    let f := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (a i))))
    have heq : f ''ᵁ ⊤ = basicOpen (a i) := by simp [f]
    rw [← heq]
    exact affineSections_finite_on_image M f G
  let t := Set.range a
  have ht : Ideal.span t = ⊤ := (iSup_basicOpen_eq_top_iff).mp ha
  let g (r : t) : Γ(M, ⊤) →ₗ[R] Γ(M, basicOpen r.1) :=
    { toFun := M.presheaf.map (basicOpen r.1).leTop.op
      map_add' := map_add _
      map_smul' := M.map_smul_Spec (basicOpen r.1).leTop.op }
  have (r : t) : IsLocalizedModule.Away r.1 (g r) := by
    change IsLocalizedModule.Away r.1
      ((modulesSpecToSheaf.obj M).obj.map (basicOpen r.1).leTop.op).hom
    exact (isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance r.1
  apply Module.Finite.of_localizationSpan' t ht g
    (Mₚ := fun r ↦ Γ(M, basicOpen r.1))
    (Rₚ := fun r ↦ Γ(Spec R, basicOpen r.1))
  rintro ⟨r, i, rfl⟩
  exact hfin i

/-- Tilde carries an algebraically finitely presented module to a locally
finitely presented module sheaf. -/
theorem affineTilde_isFinitePresentation (N : ModuleCat.{u} R)
    [Module.FinitePresentation R N] : (tilde N).IsFinitePresentation := by
  obtain ⟨s, hs, ht⟩ := Module.FinitePresentation.out (R := R) (M := N)
  obtain ⟨t, ht⟩ := ht
  let P := presentationTilde N (s : Set N) hs (t : Set (s →₀ R)) ht
  have : P.IsFinite :=
    { isFiniteType_generators := ⟨inferInstanceAs (Finite (s : Set N))⟩
      isFiniteType_relations := ⟨inferInstanceAs (Finite (t : Set (s →₀ R)))⟩ }
  exact affinePresentation_isFinitePresentation.{u, u, u} P

/-- Over a Noetherian ring, tilde of a finite module is locally finitely presented. -/
theorem affineTilde_isFinitePresentation_of_finite [IsNoetherianRing R]
    (N : ModuleCat.{u} R) [Module.Finite R N] : (tilde N).IsFinitePresentation := by
  have := Module.finitePresentation_of_finite R N
  exact affineTilde_isFinitePresentation N

/-- The affine comparison is the inverse of Mathlib's canonical counit. -/
def affineCoherentIso (M : (Spec R).Modules) [M.IsFinitePresentation] :
    M ≅ tilde (moduleSpecΓFunctor.obj M) :=
  (asIso M.fromTildeΓ).symm

@[simp]
lemma affineCoherentIso_inv (M : (Spec R).Modules) [M.IsFinitePresentation] :
    (affineCoherentIso M).inv = M.fromTildeΓ := rfl

/-- The comparison uses the counit of the actual affine equivalence. -/
lemma affineCoherentIso_counit (M : (Spec R).Modules) [M.IsFinitePresentation] :
    (affineCoherentIso M).inv =
      ((tildeEquiv (R := R)).counitIso.hom.app ⟨M, inferInstance⟩).hom := rfl

/-- The canonical comparison on the global sections of a tilde module. -/
def affineTildeSectionsEquiv (N : ModuleCat.{u} R) : N ≃ₗ[R] Γ(tilde N, ⊤) :=
  (tilde.isoTop N).toLinearEquiv

/-- On a Noetherian affine scheme, local finite presentation of a quasi-coherent
sheaf is equivalent to finiteness of its actual global sections. -/
theorem affineCoherent_iff_finite_sections [IsNoetherianRing R]
    (M : (Spec R).Modules) [M.IsQuasicoherent] :
    M.IsFinitePresentation ↔ Module.Finite R Γ(M, ⊤) := by
  refine ⟨fun _ ↦ affineCoherent_finite_sections M, fun h ↦ ?_⟩
  have : Module.Finite R (moduleSpecΓFunctor.obj M) := h
  have : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  exact (SheafOfModules.isFinitePresentation (Spec R).ringCatSheaf).prop_of_iso
    (asIso M.fromTildeΓ) (affineTilde_isFinitePresentation_of_finite (moduleSpecΓFunctor.obj M))

/-- Locally finitely presented sheaves on a Noetherian affine scheme are exactly
the sheaves associated to finite modules. -/
theorem affineCoherent_iff_exists_finite [IsNoetherianRing R] (M : (Spec R).Modules) :
    M.IsFinitePresentation ↔
      ∃ N : ModuleCat.{u} R, Module.Finite R N ∧ Nonempty (M ≅ tilde N) := by
  refine ⟨fun h ↦ ⟨moduleSpecΓFunctor.obj M, affineCoherent_finite_sections M,
    ⟨affineCoherentIso M⟩⟩, ?_⟩
  rintro ⟨N, hN, ⟨e⟩⟩
  let := hN
  exact (SheafOfModules.isFinitePresentation (Spec R).ringCatSheaf).prop_of_iso e.symm
    (affineTilde_isFinitePresentation_of_finite N)

end FLT.Mazur.FCurve
