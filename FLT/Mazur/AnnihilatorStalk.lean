/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AnnihilatorCoherence
public import FLT.Mazur.AffineStalkMorphism
public import FLT.Mazur.CoherentGenericComparison

/-!
# Actual stalks of the annihilator subsheaf

The ideal stalk is the image of the canonical ideal-module inclusion in the
structure stalk, with its original scalar action.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.FCurve.CoherentDevissage

universe u

namespace FLT.Mazur.AnnihilatorSubsheaf

variable {X : Scheme.{u}}

/-- The unit module's additive stalk is the additive group of the structure stalk. -/
def structureStalkIso (x : X) :
    (structureModule X).presheaf.stalk x ≅ AddCommGrpCat.of (X.presheaf.stalk x) :=
  (preservesColimitIso (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
    ((OpenNhds.inclusion x).op ⋙ X.presheaf)).symm

@[simp]
lemma structureStalkIso_germ (x : X) (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)) :
    (structureStalkIso x).hom ((structureModule X).presheaf.germ U x hx r) =
      X.presheaf.germ U x hx r := by
  exact congr($(ι_preservesColimitIso_inv
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
    ((OpenNhds.inclusion x).op ⋙ X.presheaf) (op ⟨U, hx⟩)) r)

/-- The canonical unit-stalk comparison preserves the structure-stalk action. -/
def structureStalkLinearEquiv (x : X) :
    (structureModule X).presheaf.stalk x ≃ₗ[X.presheaf.stalk x] X.presheaf.stalk x where
  __ := (structureStalkIso x).addCommGroupIsoToAddEquiv
  map_smul' r m := by
    obtain ⟨U, hx, a, n, rfl, rfl⟩ :=
      comparison_common_germs (structureModule X) x r m
    change (structureStalkIso x).hom (_ • _) = _ • (structureStalkIso x).hom _
    erw [← (structureModule X).val.germ_smul]
    change Γ(X, U) at n
    change (structureStalkIso x).hom
      ((structureModule X).presheaf.germ U x hx (a * n)) =
        X.presheaf.germ U x hx a *
          (structureStalkIso x).hom ((structureModule X).presheaf.germ U x hx n)
    exact (structureStalkIso_germ x U hx (a * n)).trans
      (((X.presheaf.germ U x hx).hom.map_mul a n).trans
        (congrArg (X.presheaf.germ U x hx a * ·)
          (structureStalkIso_germ x U hx n).symm))

/-- The actual ideal inclusion on stalks, with values in the actual structure stalk. -/
def idealStalkInclusion (I : X.IdealSheafData) (x : X) :
    (idealModule I).presheaf.stalk x →ₗ[X.presheaf.stalk x] X.presheaf.stalk x :=
  (structureStalkLinearEquiv x).toLinearMap.comp (comparisonStalkLinear (idealModuleι I) x)

/-- The ideal stalk is the image of the actual ideal-module stalk map. -/
def stalkIdeal (I : X.IdealSheafData) (x : X) : Ideal (X.presheaf.stalk x) :=
  LinearMap.range (idealStalkInclusion I x)

@[simp]
lemma idealStalkInclusion_germ (I : X.IdealSheafData) (x : X)
    (U : X.Opens) (hx : x ∈ U) (m : Γ(idealModule I, U)) :
    idealStalkInclusion I x ((idealModule I).presheaf.germ U x hx m) =
      X.presheaf.germ U x hx ((idealModuleι I).app U m) := by
  change (structureStalkIso x).hom (((stalk x).map (idealModuleι I)) _) = _
  exact (congrArg (structureStalkIso x).hom
    (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx (idealModuleι I).mapPresheaf m)).trans
      (structureStalkIso_germ x U hx _)

/-- A stalk element has a representative on an affine subneighborhood. -/
lemma exists_affine_germ_le (M : X.Modules) (x : X) (m : M.presheaf.stalk x)
    (U : X.Opens) (hx : x ∈ U) :
    ∃ (V : X.affineOpens) (_hVU : V.1 ≤ U) (hxV : x ∈ V.1) (n : Γ(M, V.1)),
      M.presheaf.germ V.1 x hxV n = m := by
  obtain ⟨W, hWU, hxW, n, rfl⟩ := M.presheaf.exists_le_germ_eq m hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxW W.isOpen
  refine ⟨⟨V, hV⟩, hVW.trans hWU, hxV, M.presheaf.map (homOfLE hVW).op n, ?_⟩
  exact M.presheaf.germ_res_apply (homOfLE hVW) x hxV n

/-- The actual ideal stalk is extension of the defining ideal under the actual germ map. -/
theorem stalkIdeal_eq_map (I : X.IdealSheafData) (x : X)
    (U : X.affineOpens) (hx : x ∈ U.1) :
    stalkIdeal I x = (I.ideal U).map (X.presheaf.germ U.1 x hx).hom := by
  apply le_antisymm
  · rintro r ⟨m, rfl⟩
    obtain ⟨V, hVU, hxV, n, rfl⟩ := exists_affine_germ_le (idealModule I) x m U.1 hx
    rw [idealStalkInclusion_germ]
    have hn : (idealModuleι I).app V.1 n ∈ I.ideal V :=
      (Set.ext_iff.mp (idealModuleι_range I V) _).mp ⟨n, rfl⟩
    have h := Ideal.mem_map_of_mem (X.presheaf.germ V.1 x hxV).hom hn
    rw [← I.map_ideal hVU, Ideal.map_map] at h
    have he : (X.presheaf.germ V.1 x hxV).hom.comp
        (X.presheaf.map (homOfLE hVU).op).hom = (X.presheaf.germ U.1 x hx).hom := by
      ext a
      exact X.presheaf.germ_res_apply (homOfLE hVU) x hxV a
    erw [he] at h
    exact h
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    obtain ⟨m, hm⟩ := (Set.ext_iff.mp (idealModuleι_range I U) r).mpr hr
    refine ⟨(idealModule I).presheaf.germ U.1 x hx m, ?_⟩
    rw [idealStalkInclusion_germ, hm]

section Spec

variable {R : CommRingCat.{u}}

/-- The coefficient ring acts on the actual structure stalk through its canonical germ. -/
local instance specStalkAlgebra (x : Spec R) :
    Algebra R ((Spec R).presheaf.stalk x) :=
  (show R →+* (Spec R).presheaf.stalk x from (StructureSheaf.toStalk R x).hom).toAlgebra

/-- Coefficient scalars on an actual module stalk use the structure-stalk action. -/
local instance specStalkBaseModule (M : (Spec R).Modules) (x : Spec R) :
    Module R (M.presheaf.stalk x) :=
  Module.compHom (R := (Spec R).presheaf.stalk x) _ (algebraMap R _)

/-- Restricting scalars from the structure stalk gives the coefficient action. -/
local instance specStalkBaseTower (M : (Spec R).Modules) (x : Spec R) :
    IsScalarTower R ((Spec R).presheaf.stalk x) (M.presheaf.stalk x) :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Global-section germs of an actual spectrum module are coefficient-linear. -/
def specGermLinear (M : (Spec R).Modules) (x : Spec R) :
    Γ(M, ⊤) →ₗ[R] M.presheaf.stalk x where
  __ := (M.presheaf.germ ⊤ x trivial).hom
  map_smul' r m := by
    change M.presheaf.germ ⊤ x trivial (r • m) =
      (algebraMap R ((Spec R).presheaf.stalk x) r) • M.presheaf.germ ⊤ x trivial m
    exact (M.val.germ_smul x ⊤ trivial (algebraMap R Γ(Spec R, ⊤) r) m).trans
      (congrArg (fun a : (Spec R).presheaf.stalk x ↦
        a • M.presheaf.germ ⊤ x trivial m)
          (StructureSheaf.algebraMap_germ_apply ⊤ x trivial r))

/-- The actual affine germ map is localization at the point. -/
instance specGermLinear_isLocalized (M : (Spec R).Modules) [M.IsQuasicoherent]
    (x : Spec R) : IsLocalizedModule x.asIdeal.primeCompl (specGermLinear M x) := by
  let e := (comparisonStalkEquiv (asIso M.fromTildeΓ) x).restrictScalars R
  have h := IsLocalizedModule.of_linearEquiv x.asIdeal.primeCompl
    (tilde.toStalk (moduleSpecΓFunctor.obj M) x).hom e
  have he : e.toLinearMap.comp (tilde.toStalk (moduleSpecΓFunctor.obj M) x).hom =
      specGermLinear M x := by
    ext m
    change ((stalk x).map M.fromTildeΓ)
      ((tilde (moduleSpecΓFunctor.obj M)).presheaf.germ ⊤ x trivial
        (tilde.toOpen (moduleSpecΓFunctor.obj M) ⊤ m)) = _
    have hn := TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ x trivial
      M.fromTildeΓ.mapPresheaf (tilde.toOpen (moduleSpecΓFunctor.obj M) ⊤ m)
    have ht : M.fromTildeΓ.app ⊤ (tilde.toOpen (moduleSpecΓFunctor.obj M) ⊤ m) = m := by
      simpa using! congrArg (fun f ↦ f.hom m) (M.toOpen_fromTildeΓ_app ⊤)
    exact hn.trans (congrArg (M.presheaf.germ ⊤ x trivial) ht)
  rwa [he] at h

/-- Affine stalk maps have the localized image of their actual section map. -/
theorem specStalk_range {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (a : M ⟶ N) (x : Spec R) :
    ((comparisonStalkLinear a x).restrictScalars R).range =
      (moduleSpecΓFunctor.map a).hom.range.localized₀ x.asIdeal.primeCompl
        (specGermLinear N x) := by
  have he : (comparisonStalkLinear a x).restrictScalars R =
      IsLocalizedModule.map x.asIdeal.primeCompl (specGermLinear M x)
        (specGermLinear N x) (moduleSpecΓFunctor.map a).hom := by
    apply IsLocalizedModule.linearMap_ext x.asIdeal.primeCompl
      (specGermLinear M x) (specGermLinear N x)
    rw [IsLocalizedModule.map_comp]
    ext m
    exact TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ x trivial a.mapPresheaf m
  rw [he]
  exact LinearMap.range_localizedMap_eq_localized₀_range _ _ _ _

/-- On an affine chart the constructed inclusion has the localized annihilator image. -/
theorem chart_stalk_range [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (F : X.Modules) [F.IsFinitePresentation] (U : X.affineOpens)
    (x : Spec Γ(X, U.1)) (m : (F.restrict U.2.fromSpec).presheaf.stalk x) :
    m ∈ Set.range ((stalk x).map ((restrictFunctor U.2.fromSpec).map (inclusion I F))) ↔
      m ∈ AffineAnnihilator.annihilated (I.ideal U)
        ((F.restrict U.2.fromSpec).presheaf.stalk x) := by
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have := sheaf_coherent I F
  have := coherentPresentation_restrict U.2.fromSpec (sheaf I F)
  have := coherentPresentation_restrict U.2.fromSpec F
  let a := (restrictFunctor U.2.fromSpec).map (inclusion I F)
  have he : (moduleSpecΓFunctor.map a).hom.range =
      AffineAnnihilator.annihilated (I.ideal U) Γ(F.restrict U.2.fromSpec, ⊤) := by
    ext m
    exact chart_range I F U ⊤ (isAffineOpen_top _) m
  change m ∈ ((comparisonStalkLinear a x).restrictScalars Γ(X, U.1)).range ↔ _
  rw [specStalk_range, he]
  rw [AffineAnnihilator.localized_annihilated (I.ideal U) (IsNoetherian.noetherian _)]

/-- Coefficient scalars correspond to the original affine germs under restriction. -/
lemma chart_stalk_scalar (U : X.affineOpens) (y : Spec Γ(X, U.1))
    (hy : U.2.fromSpec y ∈ U.1) (r : Γ(X, U.1)) :
    inv (U.2.fromSpec.stalkMap y)
        (algebraMap Γ(X, U.1) ((Spec Γ(X, U.1)).presheaf.stalk y) r) =
      X.presheaf.germ U.1 (U.2.fromSpec y) hy r := by
  have h := comparisonRestrictScalar_germ U.2.fromSpec y ⊤ trivial
    (algebraMap Γ(X, U.1) Γ(Spec Γ(X, U.1), ⊤) r)
  have hg := StructureSheaf.algebraMap_germ_apply ⊤ y trivial r
  have hs := chart_scalar U ⊤ r
  exact (congrArg (inv (U.2.fromSpec.stalkMap y)) hg.symm).trans
    (h.trans ((congrArg (X.presheaf.germ (U.2.fromSpec ''ᵁ ⊤)
      (U.2.fromSpec y) (by simpa using hy)) hs).trans
        (X.presheaf.germ_res_apply (homOfLE (chart_image_le U ⊤)) _ _ r)))

/-- Annihilation by the actual ideal stalk can be tested on affine ideal germs. -/
lemma mem_stalk_annihilated (I : X.IdealSheafData) (F : X.Modules) (x : X)
    (U : X.affineOpens) (hx : x ∈ U.1) (m : F.presheaf.stalk x) :
    m ∈ AffineAnnihilator.annihilated (stalkIdeal I x) (F.presheaf.stalk x) ↔
      ∀ r ∈ I.ideal U, X.presheaf.germ U.1 x hx r • m = 0 := by
  rw [stalkIdeal_eq_map I x U hx]
  change m ∈ AffineAnnihilator.annihilated (Ideal.span _) _ ↔ _
  rw [AffineAnnihilator.mem_annihilated_span]
  constructor
  · intro h r hr
    exact h _ ⟨r, hr, rfl⟩
  · rintro h _ ⟨r, hr, rfl⟩
    exact h r hr

/-- The stalk formula transported through a canonical affine chart. -/
lemma stalk_range_on_chart [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (F : X.Modules) [F.IsFinitePresentation] (U : X.affineOpens)
    (y : Spec Γ(X, U.1)) (hxV : U.2.fromSpec y ∈ U.1)
    (m : F.presheaf.stalk (U.2.fromSpec y)) :
    m ∈ Set.range ((stalk (U.2.fromSpec y)).map (inclusion I F)) ↔
      m ∈ AffineAnnihilator.annihilated (stalkIdeal I (U.2.fromSpec y))
        (F.presheaf.stalk (U.2.fromSpec y)) := by
  let e := comparisonRestrictStalk U.2.fromSpec y F
  let k := comparisonRestrictStalk U.2.fromSpec y (sheaf I F)
  obtain ⟨n, rfl⟩ := e.surjective m
  have hr : e n ∈ Set.range ((stalk (U.2.fromSpec y)).map (inclusion I F)) ↔
      n ∈ Set.range ((stalk y).map ((restrictFunctor U.2.fromSpec).map (inclusion I F))) := by
    constructor
    · rintro ⟨a, ha⟩
      obtain ⟨b, rfl⟩ := k.surjective a
      refine ⟨b, e.injective ?_⟩
      exact (comparisonRestrictStalk_naturality U.2.fromSpec y (inclusion I F) b).trans ha
    · rintro ⟨a, rfl⟩
      exact ⟨k a, (comparisonRestrictStalk_naturality U.2.fromSpec y
        (inclusion I F) a).symm⟩
  rw [hr, chart_stalk_range I F U y n, mem_stalk_annihilated I F _ U hxV]
  constructor
  · intro h r hr
    have he := comparisonRestrictStalk_smul U.2.fromSpec y F
      (algebraMap Γ(X, U.1) ((Spec Γ(X, U.1)).presheaf.stalk y) r) n
    rw [chart_stalk_scalar U y hxV] at he
    exact he.symm.trans ((congrArg e (h r hr)).trans e.map_zero)
  · intro h r hr
    apply e.injective
    change comparisonRestrictStalk U.2.fromSpec y F
      ((algebraMap Γ(X, U.1) ((Spec Γ(X, U.1)).presheaf.stalk y) r) • n) = e 0
    rw [comparisonRestrictStalk_smul, chart_stalk_scalar U y hxV, h r hr, e.map_zero]

/-- The actual inclusion has precisely the ideal-stalk annihilator as its image. -/
theorem stalk_range [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (F : X.Modules) [F.IsFinitePresentation] (x : X) (m : F.presheaf.stalk x) :
    m ∈ Set.range ((stalk x).map (inclusion I F)) ↔
      m ∈ AffineAnnihilator.annihilated (stalkIdeal I x) (F.presheaf.stalk x) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ (⊤ : X.Opens) from trivial)
      isOpen_univ
  have hy := hV.fromSpec_primeIdealOf ⟨x, hxV⟩
  generalize hV.primeIdealOf ⟨x, hxV⟩ = y at hy
  change hV.fromSpec y = x at hy
  subst x
  exact stalk_range_on_chart I F ⟨V, hV⟩ y hxV m

/-- The constructed subsheaf's actual stalk is the actual ideal-stalk annihilator. -/
def stalkEquiv [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (F : X.Modules) [F.IsFinitePresentation] (x : X) :
    (sheaf I F).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      AffineAnnihilator.annihilated (stalkIdeal I x) (F.presheaf.stalk x) :=
  LinearEquiv.ofBijective
    ((comparisonStalkLinear (inclusion I F) x).codRestrict _
      (fun m ↦ (stalk_range I F x _).mp ⟨m, rfl⟩))
    ⟨fun _ _ h ↦ (TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective
        (fun V ↦ ModuleSubobjectCoverEquality.app_injective (inclusion I F) V) x)
          (congrArg Subtype.val h),
      fun m ↦ by
        obtain ⟨n, hn⟩ := (stalk_range I F x m.val).mpr m.property
        exact ⟨n, Subtype.ext hn⟩⟩

/-- The stalk equivalence preserves the original inclusion into the ambient stalk. -/
@[simp]
lemma stalkEquiv_val [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (F : X.Modules) [F.IsFinitePresentation] (x : X) (m : (sheaf I F).presheaf.stalk x) :
    (stalkEquiv I F x m).val = (stalk x).map (inclusion I F) m := rfl

end Spec

end FLT.Mazur.AnnihilatorSubsheaf
