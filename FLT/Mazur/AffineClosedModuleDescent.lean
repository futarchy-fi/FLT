/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedImmersionModulePushforward
public import FLT.Mazur.TildePrincipalOpen

/-!
# Affine descent through a quotient ring

An ideal killing the actual global sections of a coherent affine module sheaf
induces a quotient-ring action on those sections. Their tilde sheaf on the
quotient spectrum pushes forward to the original sheaf. The construction is
functorial in sheaf maps and compatible with principal-open localization.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite PrimeSpectrum
open AlgebraicGeometry.Scheme.Modules

universe u

namespace FLT.Mazur.FCurve.CoherentDevissage.AffineClosedModuleDescent

variable {R : CommRingCat.{u}} (I : Ideal R) (M : (Spec R).Modules)

/-- The ideal acts trivially on the actual global sections, with their canonical scalars. -/
def Killed : Prop := ∀ r ∈ I, ∀ m : moduleSpecΓFunctor.obj M, r • m = 0

variable (hM : Killed I M)

/-- The quotient action is obtained by factoring the actual scalar endomorphisms. -/
def quotientAction : R ⧸ I →+* AddMonoid.End (moduleSpecΓFunctor.obj M) :=
  Ideal.Quotient.lift I (Module.toAddMonoidEnd R (moduleSpecΓFunctor.obj M))
    (fun r hr ↦ AddMonoidHom.ext (hM r hr))

/-- The actual global sections, equipped with the quotient-ring action. -/
abbrev quotientSections : ModuleCat (CommRingCat.of (R ⧸ I)) :=
  letI _quotientSectionsModule : Module (R ⧸ I) (moduleSpecΓFunctor.obj M) :=
    Module.compHom _ (quotientAction I M hM)
  ModuleCat.of (CommRingCat.of (R ⧸ I)) (moduleSpecΓFunctor.obj M)

@[simp]
lemma quotientSections_mk_smul (r : R) (m : quotientSections I M hM) :
    (Ideal.Quotient.mk I r) • m = (r • m : moduleSpecΓFunctor.obj M) := rfl

/-- Forgetting the quotient action recovers the given global-section module. -/
def quotientSectionsRestrictIso :
    (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj (quotientSections I M hM) ≅
      moduleSpecΓFunctor.obj M :=
  LinearEquiv.toModuleIso (R := R) (X₁ :=
    (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj (quotientSections I M hM))
    (X₂ := moduleSpecΓFunctor.obj M)
    { toFun := id
      invFun := id
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

/-- The descended sheaf is constructed from the original sheaf's global sections. -/
abbrev descent : (Spec (.of (R ⧸ I))).Modules := tilde (quotientSections I M hM)

/-- The closed immersion of the quotient spectrum. -/
abbrev immersion : Spec (.of (R ⧸ I)) ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))

/-- Global sections of the constructed pushforward recover the actual input sections. -/
def pushforwardSectionsIso :
    moduleSpecΓFunctor.obj ((pushforward (immersion I)).obj (descent I M hM)) ≅
      moduleSpecΓFunctor.obj M :=
  affinePushforwardSectionsIso (CommRingCat.ofHom (Ideal.Quotient.mk I)) _ ≪≫
    (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).mapIso
      (tilde.isoTop (quotientSections I M hM)).symm ≪≫
    quotientSectionsRestrictIso I M hM

/-- The sheaf-level comparison, using the two canonical affine counits. -/
def pushforwardIso [M.IsFinitePresentation] :
    (pushforward (immersion I)).obj (descent I M hM) ≅ M := by
  have := isIso_fromTildeΓ_pushforward
    (CommRingCat.ofHom (Ideal.Quotient.mk I)) (descent I M hM)
  exact (asIso ((pushforward (immersion I)).obj (descent I M hM)).fromTildeΓ).symm ≪≫
    (tilde.functor R).mapIso (pushforwardSectionsIso I M hM) ≪≫ asIso M.fromTildeΓ

/-- A map of the original sheaves is linear for the constructed quotient actions. -/
def quotientSectionsMap {N : (Spec R).Modules} (hN : Killed I N) (a : M ⟶ N) :
    quotientSections I M hM ⟶ quotientSections I N hN :=
  ModuleCat.ofHom (X := quotientSections I M hM) (Y := quotientSections I N hN)
    { toFun := (moduleSpecΓFunctor.map a).hom
      map_add' := map_add _
      map_smul' := fun q m ↦ by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
        exact (moduleSpecΓFunctor.map a).hom.map_smul r m }

/-- The descended map comes from the actual map on global sections. -/
def descentMap {N : (Spec R).Modules} (hN : Killed I N) (a : M ⟶ N) :
    descent I M hM ⟶ descent I N hN :=
  (tilde.functor _).map (quotientSectionsMap I M hM hN a)

@[simp]
lemma quotientSectionsMap_id : quotientSectionsMap I M hM hM (𝟙 M) = 𝟙 _ := by
  ext m
  exact congrArg (fun f ↦ f.hom m) (moduleSpecΓFunctor.map_id M)

@[simp]
lemma quotientSectionsMap_comp {N P : (Spec R).Modules}
    (hN : Killed I N) (hP : Killed I P) (a : M ⟶ N) (b : N ⟶ P) :
    quotientSectionsMap I M hM hP (a ≫ b) =
      quotientSectionsMap I M hM hN a ≫ quotientSectionsMap I N hN hP b := by
  ext m
  exact congrArg (fun f ↦ f.hom m) (moduleSpecΓFunctor.map_comp a b)

@[simp]
lemma descentMap_id : descentMap I M hM hM (𝟙 M) = 𝟙 _ := by
  unfold descentMap
  rw [quotientSectionsMap_id]
  exact (tilde.functor _).map_id _

@[simp]
lemma descentMap_comp {N P : (Spec R).Modules}
    (hN : Killed I N) (hP : Killed I P) (a : M ⟶ N) (b : N ⟶ P) :
    descentMap I M hM hP (a ≫ b) =
      descentMap I M hM hN a ≫ descentMap I N hN hP b := by
  unfold descentMap
  rw [quotientSectionsMap_comp]
  exact (tilde.functor _).map_comp _ _

/-- Naturality of the affine pushforward comparison on global sections. -/
lemma pushforwardSectionsIso_naturality {N : (Spec R).Modules}
    (hN : Killed I N) (a : M ⟶ N) :
    moduleSpecΓFunctor.map ((pushforward (immersion I)).map (descentMap I M hM hN a)) ≫
        (pushforwardSectionsIso I N hN).hom =
      (pushforwardSectionsIso I M hM).hom ≫ moduleSpecΓFunctor.map a := by
  have h₁ :
      moduleSpecΓFunctor.map ((pushforward (immersion I)).map (descentMap I M hM hN a)) ≫
          (affinePushforwardSectionsIso (CommRingCat.ofHom (Ideal.Quotient.mk I))
            (descent I N hN)).hom =
        (affinePushforwardSectionsIso (CommRingCat.ofHom (Ideal.Quotient.mk I))
          (descent I M hM)).hom ≫
            (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).map
              (moduleSpecΓFunctor.map (descentMap I M hM hN a)) :=
    congrArg (fun f ↦ f.hom.app (op ⊤))
      ((pushforwardCompModulesSpecToSheafIso
        (CommRingCat.ofHom (Ideal.Quotient.mk I))).hom.naturality
          (descentMap I M hM hN a))
  have h₂ : moduleSpecΓFunctor.map (descentMap I M hM hN a) ≫
      (tilde.isoTop (quotientSections I N hN)).inv =
        (tilde.isoTop (quotientSections I M hM)).inv ≫ quotientSectionsMap I M hM hN a :=
    (tilde.toTildeΓNatIso (R := CommRingCat.of (R ⧸ I))).inv.naturality
      (quotientSectionsMap I M hM hN a)
  have h₃ :
      (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).map
          (quotientSectionsMap I M hM hN a) ≫ (quotientSectionsRestrictIso I N hN).hom =
        (quotientSectionsRestrictIso I M hM).hom ≫ moduleSpecΓFunctor.map a := by
    ext m
    rfl
  dsimp only [pushforwardSectionsIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom]
  rw [← Category.assoc, ← Category.assoc, h₁]
  simp only [Category.assoc]
  congr 1
  rw [← Category.assoc, ← Functor.map_comp, h₂, Functor.map_comp]
  simp only [Category.assoc, h₃]

/-- The pushforward comparison is characterized by the canonical affine counit. -/
lemma pushforwardIso_counit [M.IsFinitePresentation] :
    ((pushforward (immersion I)).obj (descent I M hM)).fromTildeΓ ≫
        (pushforwardIso I M hM).hom =
      (tilde.functor R).map (pushforwardSectionsIso I M hM).hom ≫ M.fromTildeΓ := by
  have := isIso_fromTildeΓ_pushforward
    (CommRingCat.ofHom (Ideal.Quotient.mk I)) (descent I M hM)
  simp [pushforwardIso]

/-- The constructed descent maps recover the original sheaf maps under pushforward. -/
lemma pushforwardIso_naturality [M.IsFinitePresentation] {N : (Spec R).Modules}
    [N.IsFinitePresentation] (hN : Killed I N) (a : M ⟶ N) :
    (pushforward (immersion I)).map (descentMap I M hM hN a) ≫
        (pushforwardIso I N hN).hom = (pushforwardIso I M hM).hom ≫ a := by
  let P := (pushforward (immersion I)).obj (descent I M hM)
  let Q := (pushforward (immersion I)).obj (descent I N hN)
  let b := (pushforward (immersion I)).map (descentMap I M hM hN a)
  have := isIso_fromTildeΓ_pushforward
    (CommRingCat.ofHom (Ideal.Quotient.mk I)) (descent I M hM)
  have hc : (tilde.functor R).map (moduleSpecΓFunctor.map b) ≫ Q.fromTildeΓ =
      P.fromTildeΓ ≫ b := fromTildeΓNatTrans.naturality b
  have hd : (tilde.functor R).map (moduleSpecΓFunctor.map a) ≫ N.fromTildeΓ =
      M.fromTildeΓ ≫ a := fromTildeΓNatTrans.naturality a
  apply (cancel_epi P.fromTildeΓ).mp
  change P.fromTildeΓ ≫ (b ≫ _) = _
  rw [← Category.assoc, ← hc, Category.assoc, pushforwardIso_counit]
  rw [← Category.assoc, ← Functor.map_comp, pushforwardSectionsIso_naturality,
    Functor.map_comp, Category.assoc, hd, ← Category.assoc, ← pushforwardIso_counit,
    Category.assoc]

/-- Finite generation descends for the actual global sections. -/
lemma quotientSections_finite [M.IsFinitePresentation] :
    Module.Finite (R ⧸ I) (quotientSections I M hM) := by
  have : Module.Finite R (moduleSpecΓFunctor.obj M) := affineCoherent_finite_sections M
  let f : moduleSpecΓFunctor.obj M →ₛₗ[Ideal.Quotient.mk I] quotientSections I M hM :=
    { toFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact Module.Finite.of_surjective f Function.surjective_id

/-- Principal-open sections on the quotient are localizations of the actual input sections. -/
abbrev descentSectionsEquiv (r : R) :=
  TildePrincipalOpen.sectionsEquiv (quotientSections I M hM) (Ideal.Quotient.mk I r)

/-- A global section goes to its fraction with denominator one. -/
lemma descentSectionsEquiv_toOpen (r : R) (m : quotientSections I M hM) :
    descentSectionsEquiv I M hM r
      (TildePrincipalOpen.toSections (quotientSections I M hM) (Ideal.Quotient.mk I r) m) =
      LocalizedModule.mk m 1 :=
  TildePrincipalOpen.sectionsEquiv_toSections _ _ _

/-- The descended map on a principal open is the localized map of actual global sections. -/
lemma descentMap_localization {N : (Spec R).Modules} (hN : Killed I N)
    (a : M ⟶ N) (r : R)
    (x : TildePrincipalOpen.sections (quotientSections I M hM) (Ideal.Quotient.mk I r)) :
    descentSectionsEquiv I N hN r
      (((modulesSpecToSheaf.map (descentMap I M hM hN a)).hom.app
        (op (basicOpen (Ideal.Quotient.mk I r)))) x) =
      IsLocalizedModule.map (.powers (Ideal.Quotient.mk I r))
        (LocalizedModule.mkLinearMap _ (quotientSections I M hM))
        (LocalizedModule.mkLinearMap _ (quotientSections I N hN))
        (quotientSectionsMap I M hM hN a).hom (descentSectionsEquiv I M hM r x) :=
  TildePrincipalOpen.sectionsEquiv_naturality _ (quotientSectionsMap I M hM hN a) x

/-- The principal-open comparison respects restriction to a smaller principal open. -/
lemma descentSectionsEquiv_restriction (r s : R)
    (x : TildePrincipalOpen.sections (quotientSections I M hM) (Ideal.Quotient.mk I r)) :
    TildePrincipalOpen.sectionsEquiv (quotientSections I M hM)
      (Ideal.Quotient.mk I r * Ideal.Quotient.mk I s)
      (TildePrincipalOpen.restriction (quotientSections I M hM)
        (Ideal.Quotient.mk I r) (Ideal.Quotient.mk I s) x) =
      TildePrincipalOpen.localizationRestriction (quotientSections I M hM)
        (Ideal.Quotient.mk I r) (Ideal.Quotient.mk I s)
        (descentSectionsEquiv I M hM r x) :=
  TildePrincipalOpen.sectionsEquiv_restriction _ _ _ x

/-- Restriction of scalars of the constructed sheaf, pushed to the base spectrum. -/
abbrev quotientPushforwardSheaf : TopCat.Sheaf (ModuleCat R) (Spec R) :=
  (modulesSpecToSheaf ⋙ TopCat.Sheaf.pushforward (ModuleCat (R ⧸ I))
    (immersion I).base ⋙ sheafCompose _
      (ModuleCat.restrictScalars (Ideal.Quotient.mk I))).obj (descent I M hM)

/-- The original sheaf, as a sheaf of base-ring modules, is the constructed pushforward. -/
def sectionSheafIso [M.IsFinitePresentation] :
    modulesSpecToSheaf.obj M ≅ quotientPushforwardSheaf I M hM :=
  modulesSpecToSheaf.mapIso (pushforwardIso I M hM).symm ≪≫
    (pushforwardCompModulesSpecToSheafIso (CommRingCat.ofHom (Ideal.Quotient.mk I))).app _

/-- The comparison on `D(r)` identifies original sections with quotient-spectrum sections. -/
def principalSectionsIso [M.IsFinitePresentation] (r : R) :
    (modulesSpecToSheaf.obj M).presheaf.obj (op (basicOpen r)) ≅
      (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
        (TildePrincipalOpen.sections (quotientSections I M hM) (Ideal.Quotient.mk I r)) :=
  (TopCat.Sheaf.forget (ModuleCat R) (Spec R) ⋙
    (evaluation _ _).obj (op (basicOpen r))).mapIso
    (sectionSheafIso I M hM)

/-- The base-linear form of the principal-open localization comparison. -/
def tildeSectionsLocalizationIso {S : CommRingCat.{u}}
    (A : ModuleCat.{u} S) (s : S) :
    TildePrincipalOpen.sections A s ≅ ModuleCat.of S (LocalizedModule (.powers s) A) :=
  ((TildePrincipalOpen.sectionsEquiv A s).restrictScalars S).toModuleIso

/-- In particular, original principal-open sections are localized quotient modules. -/
def principalLocalizationIso [M.IsFinitePresentation] (r : R) :
    (modulesSpecToSheaf.obj M).presheaf.obj (op (basicOpen r)) ≅
      (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
        (ModuleCat.of (CommRingCat.of (R ⧸ I))
          (LocalizedModule (.powers (Ideal.Quotient.mk I r)) (quotientSections I M hM))) :=
  principalSectionsIso I M hM r ≪≫
    (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).mapIso
      (tildeSectionsLocalizationIso (quotientSections I M hM) (Ideal.Quotient.mk I r))


/-- Compatibility of the geometric comparison with restriction to `D(rs)`. -/
lemma principalSectionsIso_restriction [M.IsFinitePresentation] (r s : R)
    (x : (modulesSpecToSheaf.obj M).presheaf.obj (op (basicOpen r))) :
    (principalSectionsIso I M hM (r * s)).hom
      ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (basicOpen_mul_le_left r s)).op x) =
      (quotientPushforwardSheaf I M hM).presheaf.map
        (homOfLE (basicOpen_mul_le_left r s)).op ((principalSectionsIso I M hM r).hom x) :=
  congrArg (fun f ↦ f.hom x) ((sectionSheafIso I M hM).hom.hom.naturality
    (homOfLE (basicOpen_mul_le_left r s)).op)


end FLT.Mazur.FCurve.CoherentDevissage.AffineClosedModuleDescent
