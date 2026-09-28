/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealModuleSheaf

/-!
# The module-valued dual presheaf

Sections of the dual on an open are morphisms from the restricted module sheaf
to the structure module. Scalars act after restriction to every subopen.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

variable {X : Scheme.{u}} (M : X.Modules)

/-- Sections of the sheaf dual, before imposing its sheaf condition. -/
abbrev ModuleDualSections (U : X.Opens) :=
  M.restrict U.ι ⟶ structureModule U.toScheme

/-- Multiply a sheaf morphism by a section, restricted to every subopen. -/
def moduleDualSMul (U : X.Opens) (r : Γ(X, U))
    (φ : ModuleDualSections M U) : ModuleDualSections M U :=
  ⟨PresheafOfModules.homMk
    { app W := AddCommGrpCat.ofHom
        { toFun := fun s ↦ ((U.ι.appIso W.unop).hom
            (X.presheaf.map (homOfLE (U.ι_image_le W.unop)).op r)) • φ.app W.unop s
          map_zero' := by simp
          map_add' := by intros; simp [mul_add] }
      naturality := fun W Z f ↦ by
        ext s
        have h := congr($(φ.mapPresheaf.naturality f) s)
        change φ.app Z.unop ((M.restrict U.ι).presheaf.map f s) =
          U.toScheme.presheaf.map f (φ.app W.unop s) at h
        change ((U.ι.appIso Z.unop).hom
          (X.presheaf.map (homOfLE (U.ι_image_le Z.unop)).op r)) •
            φ.app Z.unop ((M.restrict U.ι).presheaf.map f s) =
          (structureModule U.toScheme).presheaf.map f
            (((U.ι.appIso W.unop).hom
              (X.presheaf.map (homOfLE (U.ι_image_le W.unop)).op r)) • φ.app W.unop s)
        erw [Scheme.Modules.map_smul (structureModule U.toScheme) f.unop]
        rw [h]
        congr 1
        simp only [Scheme.Opens.ι_appIso, Iso.refl_hom]
        change X.presheaf.map (homOfLE (U.ι_image_le Z.unop)).op r =
          X.presheaf.map (U.ι.opensFunctor.map f.unop).op
            (X.presheaf.map (homOfLE (U.ι_image_le W.unop)).op r)
        exact congr($(X.presheaf.map_comp
          (homOfLE (U.ι_image_le W.unop)).op
          (U.ι.opensFunctor.map f.unop).op) r)
    }
    (fun W r' s ↦ by
      change Γ(U.toScheme, W.unop) at r'
      change ((U.ι.appIso W.unop).hom
        (X.presheaf.map (homOfLE (U.ι_image_le W.unop)).op r)) •
          φ.app W.unop (r' • s) = r' •
            (((U.ι.appIso W.unop).hom
              (X.presheaf.map (homOfLE (U.ι_image_le W.unop)).op r)) • φ.app W.unop s)
      rw [Scheme.Modules.Hom.app_smul]
      exact smul_comm _ _ _)⟩

instance moduleDualSectionsSMul (U : X.Opens) :
    SMul Γ(X, U) (ModuleDualSections M U) := ⟨moduleDualSMul M U⟩

@[simp]
lemma moduleDualSections_smul_app (U : X.Opens) (r : Γ(X, U))
    (φ : ModuleDualSections M U) (W : U.toScheme.Opens) (s : Γ(M.restrict U.ι, W)) :
    (r • φ).app W s =
      ((U.ι.appIso W).hom
        (X.presheaf.map (homOfLE (U.ι_image_le W)).op r)) • φ.app W s := rfl

instance moduleDualSectionsModule (U : X.Opens) :
    Module Γ(X, U) (ModuleDualSections M U) where
  one_smul φ := by ext W s; simp
  mul_smul r t φ := by ext W s; simp [mul_assoc]
  smul_zero r := by ext W s; simp
  smul_add r φ ψ := by ext W s; simp [mul_add]
  add_smul r t φ := by ext W s; simp [add_mul]
  zero_smul φ := by ext W s; simp

/-- Restrict a dual section along an inclusion of opens. -/
def moduleDualRestrict {U V : X.Opens} (h : V ≤ U)
    (φ : ModuleDualSections M U) : ModuleDualSections M V :=
  (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h).symm).hom.app M ≫
    (Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).hom.app M ≫
    (Scheme.Modules.restrictFunctor (X.homOfLE h)).map φ ≫
    (Scheme.Modules.restrictUnitIso (X.homOfLE h)).hom

/-- Evaluation of restriction on a subopen, including the canonical transports. -/
lemma moduleDualRestrict_app {U V : X.Opens} (h : V ≤ U)
    (φ : ModuleDualSections M U) (W : V.toScheme.Opens) :
    (moduleDualRestrict M h φ).app W =
      M.presheaf.map (eqToHom (show U.ι ''ᵁ X.homOfLE h ''ᵁ W = V.ι ''ᵁ W by
        simp [← Scheme.Hom.comp_image])).op ≫
      φ.app (X.homOfLE h ''ᵁ W) ≫
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat Ab).map ((X.homOfLE h).appIso W).hom := by
  simp only [moduleDualRestrict, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.restrictFunctorCongr_hom_app_app,
    Scheme.Modules.restrictFunctorComp_hom_app_app]
  change _ ≫ _ ≫ φ.app _ ≫ _ = _
  rw [← Category.assoc, ← Category.assoc, ← M.presheaf.map_comp]
  rfl

@[simp]
lemma moduleDualRestrict_add {U V : X.Opens} (h : V ≤ U)
    (φ ψ : ModuleDualSections M U) :
    moduleDualRestrict M h (φ + ψ) = moduleDualRestrict M h φ +
      moduleDualRestrict M h ψ := by
  ext W s
  simp only [moduleDualRestrict_app, Scheme.Modules.Hom.add_app,
    Preadditive.comp_add, Preadditive.add_comp]

@[simp]
lemma moduleDualRestrict_id (U : X.Opens) (φ : ModuleDualSections M U) :
    moduleDualRestrict M le_rfl φ = φ := by
  apply Scheme.Modules.hom_ext
  intro W
  rw [moduleDualRestrict_app]
  have he : X.homOfLE (show U ≤ U from le_rfl) ''ᵁ W = W := by simp
  have hn := φ.mapPresheaf.naturality (eqToHom he).op
  change (M.restrict U.ι).presheaf.map (eqToHom he).op ≫ φ.app _ =
    φ.app W ≫ (structureModule U.toScheme).presheaf.map (eqToHom he).op at hn
  simp only [Scheme.Hom.appIso_hom', Scheme.homOfLE_appLE]
  change (M.restrict U.ι).presheaf.map (eqToHom he).op ≫ φ.app _ ≫
    (structureModule U.toScheme).presheaf.map (eqToHom he.symm).op = _
  rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp]
  simp

/-- Evaluate restriction using any equal choice of its image subopen. -/
lemma moduleDualRestrict_app_eq {U V : X.Opens} (h : V ≤ U)
    (φ : ModuleDualSections M U) (W : V.toScheme.Opens) (T : U.toScheme.Opens)
    (e : X.homOfLE h ''ᵁ W = T) :
    (moduleDualRestrict M h φ).app W =
      M.presheaf.map (homOfLE (show U.ι ''ᵁ T ≤ V.ι ''ᵁ W by
        subst T; simp [← Scheme.Hom.comp_image])).op ≫ φ.app T ≫
      (structureModule X).presheaf.map (homOfLE (show V.ι ''ᵁ W ≤ U.ι ''ᵁ T by
        subst T; simp [← Scheme.Hom.comp_image])).op := by
  subst T
  rw [moduleDualRestrict_app]
  simp only [Scheme.Hom.appIso_hom', Scheme.homOfLE_appLE]
  rfl

/-- Restriction of dual sections is transitive. -/
lemma moduleDualRestrict_comp {U V Z : X.Opens} (h : V ≤ U) (g : Z ≤ V)
    (φ : ModuleDualSections M U) :
    moduleDualRestrict M g (moduleDualRestrict M h φ) =
      moduleDualRestrict M (g.trans h) φ := by
  apply Scheme.Modules.hom_ext
  intro W
  have he : X.homOfLE (g.trans h) ''ᵁ W =
      X.homOfLE h ''ᵁ X.homOfLE g ''ᵁ W := by
    simp [← Scheme.Hom.comp_image]
  rw [moduleDualRestrict_app_eq M (g.trans h) φ W _ he,
    moduleDualRestrict_app_eq M g _ W _ rfl,
    moduleDualRestrict_app_eq M h φ _ _ rfl]
  simp only [← Category.assoc]
  rw [← M.presheaf.map_comp]
  simp only [Category.assoc]
  rw [← (structureModule X).presheaf.map_comp]
  rfl

/-- Dual restriction is semilinear over the restriction of functions. -/
lemma moduleDualRestrict_smul {U V : X.Opens} (h : V ≤ U)
    (r : Γ(X, U)) (φ : ModuleDualSections M U) :
    moduleDualRestrict M h (r • φ) =
      X.presheaf.map (homOfLE h).op r • moduleDualRestrict M h φ := by
  ext W s
  rw [moduleDualRestrict_app_eq M h (r • φ) W _ rfl]
  simp only [ConcreteCategory.comp_apply, moduleDualSections_smul_app]
  rw [moduleDualRestrict_app_eq M h φ W _ rfl]
  simp only [Scheme.Opens.ι_appIso, Iso.refl_hom,
    ConcreteCategory.comp_apply]
  erw [Scheme.Modules.map_smul]
  congr 1
  simp only [Scheme.Opens.ι_appIso, Iso.refl_hom]
  change (X.presheaf.map _ ≫ X.presheaf.map _) r =
    (X.presheaf.map _ ≫ X.presheaf.map _) r
  rw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
  rfl

/-- The additive presheaf of morphisms into the structure module. -/
def moduleDualAddPresheaf : TopCat.Presheaf Ab X where
  obj U := AddCommGrpCat.of (ModuleDualSections M U.unop)
  map f := AddCommGrpCat.ofHom
    { toFun := moduleDualRestrict M (leOfHom f.unop)
      map_zero' := by
        apply Scheme.Modules.hom_ext
        intro W
        simp [moduleDualRestrict_app]
      map_add' := moduleDualRestrict_add M (leOfHom f.unop) }
  map_id U := by
    ext φ : 2
    exact moduleDualRestrict_id M U.unop φ
  map_comp f g := by
    ext φ : 2
    exact (moduleDualRestrict_comp M (leOfHom f.unop) (leOfHom g.unop) φ).symm

instance moduleDualAddPresheafModule (U : X.Opensᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj U) ((moduleDualAddPresheaf M).obj U) :=
  moduleDualSectionsModule M U.unop

/-- The intrinsic dual presheaf, with sheaf morphisms as its sections. -/
def moduleDualPresheaf : X.PresheafOfModules :=
  PresheafOfModules.ofPresheaf (moduleDualAddPresheaf M)
    (fun _ _ f r φ ↦ moduleDualRestrict_smul M (leOfHom f.unop) r φ)

/-- The dual presheaf's restriction is restriction of module-sheaf morphisms. -/
@[simp]
lemma moduleDualPresheaf_map {U V : X.Opens} (h : V ≤ U)
    (φ : ModuleDualSections M U) :
    (moduleDualPresheaf M).map (homOfLE h).op φ = moduleDualRestrict M h φ := rfl

end FLT.Mazur.FCurve
