/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineModuleSupport

/-!
# Coordinates for affine stalk morphisms

The localization comparison is natural in coefficient maps. Structure-stalk-linear
maps have compatible coefficient-linear coordinates, and restriction preserves these
coordinates through the canonical restriction-stalk comparison.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace FLT.Mazur.FCurve.CoherentDevissage

variable {R : CommRingCat.{u}} {M N : ModuleCat.{u} R}

/-- Germs on an affine scheme are linear over the coefficient ring. -/
def tildeGermLinear (M : ModuleCat R) (U : (Spec R).Opens) (x : PrimeSpectrum R)
    (hx : x ∈ U) : (modulesSpecToSheaf.obj (tilde M)).presheaf.obj (.op U) →ₗ[R]
      (tilde M).presheaf.stalk x where
  __ := ((tilde M).presheaf.germ U x hx).hom
  map_smul' r m := by
    change (tilde M).presheaf.germ U x hx (r • m) =
      StructureSheaf.toStalk R x r • ((tilde M).presheaf.germ U x hx m)
    rw [← StructureSheaf.algebraMap_germ_apply U x hx]
    exact ((tilde M).val.germ_smul x U hx (algebraMap R Γ(Spec R, U) r) m)

/-- A morphism of tilde sheaves induces an `R`-linear map on actual stalks. -/
def tildeStalkMap (f : tilde M ⟶ tilde N) (x : PrimeSpectrum R) :
    (tilde M).presheaf.stalk x →ₗ[R] (tilde N).presheaf.stalk x where
  __ := ((stalk (X := Spec R) x).map f).hom
  map_smul' r m := by
    obtain ⟨U, hx, m, rfl⟩ := (tilde M).presheaf.exists_germ_eq m
    change ((stalk (X := Spec R) x).map f) (r • tildeGermLinear M U x hx m) = _
    rw [← map_smul]
    have hg (n : Γ(tilde M, U)) :
        ((stalk (X := Spec R) x).map f) ((tilde M).presheaf.germ U x hx n) =
          (tilde N).presheaf.germ U x hx (f.app U n) :=
      TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx f.mapPresheaf n
    change ((stalk (X := Spec R) x).map f) ((tilde M).presheaf.germ U x hx (r • m)) =
      @SMul.smul R ((tilde N).presheaf.stalk x) _ r
        (((stalk (X := Spec R) x).map f) ((tilde M).presheaf.germ U x hx m))
    rw [hg, hg]
    change tildeGermLinear N U x hx (f.app U (r • m)) =
      r • tildeGermLinear N U x hx (f.app U m)
    rw [← map_smul]
    exact congrArg (tildeGermLinear N U x hx)
      (((modulesSpecToSheaf.map f).hom.app (.op U)).hom.map_smul r m)

/-- Naturality on coefficient germs. -/
@[simp]
lemma tildeStalkMap_toStalk (a : M ⟶ N) (x : PrimeSpectrum R) (m : M) :
    tildeStalkMap (tilde.map a) x (tilde.toStalk M x m) =
      tilde.toStalk N x (a m) := by
  change ((stalk (X := Spec R) x).map (tilde.map a))
    ((tilde M).presheaf.germ ⊤ x trivial (tilde.toOpen M ⊤ m)) = _
  refine (TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ x trivial
    (tilde.map a).mapPresheaf (tilde.toOpen M ⊤ m)).trans ?_
  exact congrArg ((tilde N).presheaf.germ ⊤ x trivial)
    (congrArg (fun f ↦ f m) (tilde.toOpen_map_app a ⊤))

/-- Localization uniqueness identifies the induced stalk map. -/
lemma tildeStalkMap_eq_localized (a : M ⟶ N) (x : PrimeSpectrum R) :
    tildeStalkMap (tilde.map a) x =
      IsLocalizedModule.map x.asIdeal.primeCompl
        (tilde.toStalk M x).hom (tilde.toStalk N x).hom a.hom := by
  apply IsLocalizedModule.linearMap_ext x.asIdeal.primeCompl
    (tilde.toStalk M x).hom (tilde.toStalk N x).hom
  rw [IsLocalizedModule.map_comp]
  ext m
  exact tildeStalkMap_toStalk a x m

/-- The canonical stalk comparison is natural in coefficient maps. -/
lemma tildeStalkEquiv_naturality (a : M ⟶ N) (x : PrimeSpectrum R)
    (m : (tilde M).presheaf.stalk x) :
    tildeStalkEquiv N x (tildeStalkMap (tilde.map a) x m) =
      IsLocalizedModule.map x.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap x.asIdeal.primeCompl M)
        (LocalizedModule.mkLinearMap x.asIdeal.primeCompl N) a.hom
        (tildeStalkEquiv M x m) := by
  rw [tildeStalkMap_eq_localized]
  apply (IsLocalizedModule.iso x.asIdeal.primeCompl (tilde.toStalk N x).hom).injective
  simpa [tildeStalkEquiv] using!
    DFunLike.congr_fun (IsLocalizedModule.map_iso_commute x.asIdeal.primeCompl
      (tilde.toStalk M x).hom (tilde.toStalk N x).hom a.hom) (tildeStalkEquiv M x m)

/-- Forget only the extra scalars of a prescribed structure-stalk-linear map. -/
def stalkMapBaseLinear (x : PrimeSpectrum R)
    (f : (tilde M).presheaf.stalk x →ₗ[(structurePresheafInCommRingCat R).stalk x]
      (tilde N).presheaf.stalk x) :
    (tilde M).presheaf.stalk x →ₗ[R] (tilde N).presheaf.stalk x where
  __ := f.toAddMonoidHom
  map_smul' r m := f.map_smul (StructureSheaf.toStalk R x r) m

/-- Localization coordinates of any prescribed structure-stalk-linear map. -/
def stalkMapCoordinates (x : PrimeSpectrum R)
    (f : (tilde M).presheaf.stalk x →ₗ[(structurePresheafInCommRingCat R).stalk x]
      (tilde N).presheaf.stalk x) :
    LocalizedModule x.asIdeal.primeCompl M →ₗ[R]
      LocalizedModule x.asIdeal.primeCompl N :=
  (tildeStalkEquiv N x).toLinearMap.comp
    ((stalkMapBaseLinear x f).comp (tildeStalkEquiv M x).symm.toLinearMap)

@[simp]
lemma stalkMapCoordinates_apply (x : PrimeSpectrum R)
    (f : (tilde M).presheaf.stalk x →ₗ[(structurePresheafInCommRingCat R).stalk x]
      (tilde N).presheaf.stalk x) (m : (tilde M).presheaf.stalk x) :
    stalkMapCoordinates x f (tildeStalkEquiv M x m) = tildeStalkEquiv N x (f m) := by
  simp [stalkMapCoordinates, stalkMapBaseLinear]

/-- Equality of structure-stalk-linear maps can be tested on coefficient germs. -/
lemma stalkMap_ext (x : PrimeSpectrum R)
    (f g : (tilde M).presheaf.stalk x →ₗ[(structurePresheafInCommRingCat R).stalk x]
      (tilde N).presheaf.stalk x)
    (h : ∀ m, f (tilde.toStalk M x m) = g (tilde.toStalk M x m)) : f = g := by
  have e : stalkMapBaseLinear x f = stalkMapBaseLinear x g := by
    apply IsLocalizedModule.linearMap_ext x.asIdeal.primeCompl
      (tilde.toStalk M x).hom (tilde.toStalk N x).hom
    ext m
    exact h m
  exact LinearMap.ext fun m ↦ DFunLike.congr_fun e m

/-- Canonical additive comparison for a restricted affine stalk. -/
def affineRestrictStalkEquiv (U : (Spec R).Opens) (x : U) (M : ModuleCat R) :
    ((tilde M).restrict U.ι).presheaf.stalk x ≃+ (tilde M).presheaf.stalk x.1 :=
  ((Scheme.Modules.restrictStalkNatIso U.ι x).app (tilde M)).addCommGroupIsoToAddEquiv

/-- The restriction comparison sends a germ to the same germ on the image open. -/
@[simp]
lemma affineRestrictStalkEquiv_germ (U : (Spec R).Opens) (x : U) (M : ModuleCat R)
    (V : U.toScheme.Opens) (hx : x ∈ V) (m : Γ((tilde M).restrict U.ι, V)) :
    affineRestrictStalkEquiv U x M (((tilde M).restrict U.ι).presheaf.germ V x hx m) =
      (tilde M).presheaf.germ (U.ι ''ᵁ V) x.1 (by simpa) m :=
  congrArg (fun f ↦ f m) (Scheme.Modules.germ_restrictStalkNatIso_hom_app U.ι x
    (tilde M) hx)

/-- Coefficient scalars on the restricted stalk, transported by its canonical comparison. -/
instance affineRestrictStalkModule (U : (Spec R).Opens) (x : U) (M : ModuleCat R) :
    Module R (((tilde M).restrict U.ι).presheaf.stalk x) :=
  (affineRestrictStalkEquiv U x M).module R

/-- The restriction comparison is linear for the transported coefficient action. -/
def affineRestrictStalkLinearEquiv (U : (Spec R).Opens) (x : U) (M : ModuleCat R) :
    ((tilde M).restrict U.ι).presheaf.stalk x ≃ₗ[R] (tilde M).presheaf.stalk x.1 where
  __ := affineRestrictStalkEquiv U x M
  map_smul' _ _ := (affineRestrictStalkEquiv U x M).apply_symm_apply _

/-- Localization coordinates for the actual stalk of the restricted tilde sheaf. -/
def affineRestrictStalkCoordinates (U : (Spec R).Opens) (x : U) (M : ModuleCat R) :
    ((tilde M).restrict U.ι).presheaf.stalk x ≃ₗ[R]
      LocalizedModule x.1.asIdeal.primeCompl M :=
  (affineRestrictStalkLinearEquiv U x M).trans (tildeStalkEquiv M x.1)

/-- Restricting a sheaf morphism preserves its stalk map in the canonical coordinates. -/
lemma affineRestrictStalkEquiv_naturality (U : (Spec R).Opens) (x : U)
    (f : tilde M ⟶ tilde N) (m : ((tilde M).restrict U.ι).presheaf.stalk x) :
    affineRestrictStalkEquiv U x N
      ((stalk (X := U.toScheme) x).map ((Scheme.Modules.restrictFunctor U.ι).map f) m) =
        tildeStalkMap f x.1 (affineRestrictStalkEquiv U x M m) :=
  congrArg (fun f ↦ f m) ((Scheme.Modules.restrictStalkNatIso U.ι x).hom.naturality f)

/-- Restriction and coefficient localization give the same stalk coordinates. -/
lemma affineRestrictStalkCoordinates_naturality (U : (Spec R).Opens) (x : U)
    (a : M ⟶ N) (m : ((tilde M).restrict U.ι).presheaf.stalk x) :
    affineRestrictStalkCoordinates U x N
      ((stalk (X := U.toScheme) x).map
        ((Scheme.Modules.restrictFunctor U.ι).map (tilde.map a)) m) =
      IsLocalizedModule.map x.1.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl M)
        (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl N) a.hom
        (affineRestrictStalkCoordinates U x M m) := by
  change tildeStalkEquiv N x.1 (affineRestrictStalkEquiv U x N _) = _
  rw [affineRestrictStalkEquiv_naturality, tildeStalkEquiv_naturality]
  rfl

end FLT.Mazur.FCurve.CoherentDevissage
