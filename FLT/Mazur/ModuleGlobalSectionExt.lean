/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleGlobalSectionPullback
public import FLT.Mazur.ModuleSheafMorphismGluing
/-!
# Extensionality of global module sections

Evaluation at one determines a morphism from the structure module. Pullback
along an open immersion agrees with sheaf restriction, so global sections
are determined by their pullbacks to an open cover.
-/

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X Y : Scheme.{u}}
/-- A morphism from the structure module is determined by its global value at one. -/
lemma globalSection_hom_ext {M : X.Modules} (s t : structureModule X ⟶ M)
    (h : s.app ⊤ (1 : Γ(X, ⊤)) = t.app ⊤ (1 : Γ(X, ⊤))) : s = t := by
  apply Scheme.Modules.hom_ext
  intro U
  ext r
  change Γ(X, U) at r
  have hs := congrArg (fun k ↦ k (1 : Γ(X, ⊤)))
    (s.mapPresheaf.naturality (homOfLE (show U ≤ ⊤ from le_top)).op)
  have ht := congrArg (fun k ↦ k (1 : Γ(X, ⊤)))
    (t.mapPresheaf.naturality (homOfLE (show U ≤ ⊤ from le_top)).op)
  change s.app U (X.presheaf.map _ 1) = M.presheaf.map _ (s.app ⊤ (1 : Γ(X, ⊤))) at hs
  change t.app U (X.presheaf.map _ 1) = M.presheaf.map _ (t.app ⊤ (1 : Γ(X, ⊤))) at ht
  simp only [map_one] at hs ht
  have he : s.app U (1 : Γ(X, U)) = t.app U (1 : Γ(X, U)) :=
    hs.trans ((congrArg (M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op) h).trans ht.symm)
  have hrs := s.app_smul r (1 : Γ(X, U))
  have hrt := t.app_smul r (1 : Γ(X, U))
  simpa only [smul_eq_mul, mul_one] using hrs.trans ((congrArg (r • ·) he).trans hrt.symm)

/-- Open-immersion pullback is restriction followed by the chosen comparison. -/
lemma pullGlobal_restrict (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules)
    (s : Γ(M, ⊤)) :
    ((restrictFunctorIsoPullback f).hom.app M).app ⊤
      (M.presheaf.map (homOfLE (show f ''ᵁ ⊤ ≤ ⊤ from le_top)).op s) =
        pullGlobal f M s := by
  exact congrArg (fun k ↦ k.app ⊤ s)
    (Adjunction.unit_leftAdjointUniq_hom_app (restrictAdjunction f)
      (pullbackPushforwardAdjunction f) M)

/-- Global sections are determined by their pullbacks to an open cover. -/
lemma pullGlobal_openCover_ext (C : X.OpenCover) (M : X.Modules) (s t : Γ(M, ⊤))
    (h : ∀ i, pullGlobal (C.f i) M s = pullGlobal (C.f i) M t) : s = t := by
  refine TopCat.Sheaf.eq_of_locally_eq'
    (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
    (fun i ↦ C.f i ''ᵁ ⊤) ⊤ (fun _ ↦ homOfLE le_top) (by
      simp only [Scheme.Hom.image_top_eq_opensRange]
      exact le_of_eq C.iSup_opensRange.symm) s t ?_
  intro i
  apply (ConcreteCategory.bijective_of_isIso
    (((restrictFunctorIsoPullback (C.f i)).hom.app M).app ⊤)).injective
  simpa only [pullGlobal_restrict] using h i
/-- A global section defines multiplication by its restrictions on every open. -/
def globalSectionHom (M : X.Modules) (s : Γ(M, ⊤)) : structureModule X ⟶ M :=
  (SheafOfModules.unitHomEquiv M).symm <|
    PresheafOfModules.sectionsMk
      (fun V ↦ M.presheaf.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op s)
      (fun V W f ↦ by
        change (M.presheaf.map _ ≫ M.presheaf.map _) s = _
        rw [← M.presheaf.map_comp]
        rfl)
/-- The global section morphism recovers the original section at one. -/
lemma globalSectionHom_top (M : X.Modules) (s : Γ(M, ⊤)) :
    (globalSectionHom M s).app ⊤ (1 : Γ(X, ⊤)) = s := by
  change (1 : Γ(X, ⊤)) • (M.presheaf.map (𝟙 (op ⊤)) s) = s
  rw [M.presheaf.map_id, ConcreteCategory.id_apply, one_smul]
end FLT.Mazur.FCurve
