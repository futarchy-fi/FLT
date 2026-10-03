/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealModulePullback
public import FLT.Mazur.ModulePullbackRestrictionPasting
/-!
# Restriction of the ideal-module pullback comparison

Commuting squares of open immersions preserve the canonical comparison and
its inclusion. This detects local invertibility, including off the divisor.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
namespace FLT.Mazur.FCurve
variable {X Y : Scheme.{u}}
variable {Z W : Scheme.{u}}

/-- Equality transport preserves the ideal inclusion. -/
lemma idealModule_eqToHom_ι {I J : X.IdealSheafData} (h : I = J) :
    eqToHom (congrArg idealModule h) ≫ idealModuleι J = idealModuleι I := by
  subst J
  simp

/-- Identify the pulled-back module with an explicitly equal target ideal. -/
def idealModulePullbackIsoOfEq (I : Y.IdealSheafData) (f : X ⟶ Y)
    (J : X.IdealSheafData) (h : I.comap f = J)
    [IsIso (idealModulePullbackHom I f)] :
    (Scheme.Modules.pullback f).obj (idealModule I) ≅ idealModule J :=
  asIso (idealModulePullbackHom I f) ≪≫ eqToIso (congrArg idealModule h)

/-- Equality transport in the target retains the pulled-back inclusion. -/
@[reassoc]
lemma idealModulePullbackIsoOfEq_ι (I : Y.IdealSheafData) (f : X ⟶ Y)
    (J : X.IdealSheafData) (h : I.comap f = J)
    [IsIso (idealModulePullbackHom I f)] :
    (idealModulePullbackIsoOfEq I f J h).hom ≫ idealModuleι J =
      idealModulePullbackι I f := by
  subst J
  simp [idealModulePullbackIsoOfEq]

/-- Comap ideals agree in a commuting square. -/
lemma idealModulePullback_comap_square (I : Y.IdealSheafData)
    (f : X ⟶ Y) (g : Z ⟶ W) (i : Z ⟶ X) (j : W ⟶ Y)
    (h : i ≫ f = g ≫ j) : (I.comap f).comap i = (I.comap j).comap g := by
  rw [← Scheme.IdealSheafData.comap_comp, h, Scheme.IdealSheafData.comap_comp]

/-- The canonical comparison is compatible with a commuting open square. -/
lemma idealModulePullbackHom_restrict (I : Y.IdealSheafData)
    (f : X ⟶ Y) (g : Z ⟶ W) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] (h : i ≫ f = g ≫ j) :
    (restrictFunctor i).map (idealModulePullbackHom I f) ≫
      idealModuleRestrictHom (I.comap f) i ≫
        eqToHom (congrArg idealModule (idealModulePullback_comap_square I f g i j h)) =
    (modulePullbackRestrictIso f g i j h (idealModule I)).hom ≫
      (Scheme.Modules.pullback g).map (idealModuleRestrictHom I j) ≫
        idealModulePullbackHom (I.comap j) g := by
  apply (cancel_mono (idealModuleι ((I.comap j).comap g))).mp
  simp only [Category.assoc]
  erw [idealModule_eqToHom_ι (idealModulePullback_comap_square I f g i j h)]
  rw [idealModuleRestrictHom_ι, idealModulePullbackHom_ι]
  dsimp only [idealModuleRestrictι, idealModulePullbackι]
  rw [← Functor.map_comp_assoc, idealModulePullbackHom_ι]
  dsimp only [idealModulePullbackι]
  simp only [Functor.map_comp, Category.assoc]
  rw [← (Scheme.Modules.pullback g).map_comp_assoc, idealModuleRestrictHom_ι]
  dsimp only [idealModuleRestrictι]
  simp only [Functor.map_comp, Category.assoc]
  rw [← modulePullbackRestrictIso_naturality_assoc,
    modulePullbackRestrictIso_unit]

/-- An invertible comparison on an open square gives an invertible restriction. -/
lemma idealModulePullbackHom_isIso_restrict (I : Y.IdealSheafData)
    (f : X ⟶ Y) (g : Z ⟶ W) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] (h : i ≫ f = g ≫ j)
    [IsIso (idealModulePullbackHom (I.comap j) g)] :
    IsIso ((restrictFunctor i).map (idealModulePullbackHom I f)) := by
  have : IsIso ((restrictFunctor i).map (idealModulePullbackHom I f) ≫
      idealModuleRestrictHom (I.comap f) i ≫
        eqToHom (congrArg idealModule (idealModulePullback_comap_square I f g i j h))) := by
    rw [idealModulePullbackHom_restrict I f g i j h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (idealModuleRestrictHom (I.comap f) i ≫
    eqToHom (congrArg idealModule (idealModulePullback_comap_square I f g i j h)))

/-- The comparison is invertible over the complement of the divisor support. -/
lemma idealModulePullbackHom_offSupport (I : Y.IdealSheafData) (f : X ⟶ Y) :
    IsIso ((restrictFunctor (f ⁻¹ᵁ I.support.compl).ι).map
      (idealModulePullbackHom I f)) := by
  let U : Y.Opens := I.support.compl
  have ht : I.comap U.ι = ⊤ := by
    apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
    rw [Scheme.IdealSheafData.support_comap]
    ext x
    change (x.val ∈ I.support ↔ False)
    exact iff_false_intro x.property
  have : IsIso (idealModulePullbackHom (I.comap U.ι)
      (f ∣_ I.support.compl)) := by
    rw [ht]
    infer_instance
  exact idealModulePullbackHom_isIso_restrict I f (f ∣_ I.support.compl)
    (f ⁻¹ᵁ I.support.compl).ι U.ι (morphismRestrict_ι f _).symm

/-- Invertibility along an open immersion holds on its image open. -/
lemma moduleHom_isIso_restrict_opensRange {M N : X.Modules} (a : M ⟶ N)
    (i : Z ⟶ X) [IsOpenImmersion i] [IsIso ((restrictFunctor i).map a)] :
    IsIso ((restrictFunctor i.opensRange.ι).map a) := by
  apply Hom.isIso_iff_isIso_app.mpr
  intro U
  have hi : IsIso (((restrictFunctor i).map a).app
      (i ⁻¹ᵁ (i.opensRange.ι ''ᵁ U))) := inferInstance
  change IsIso (a.app (i ''ᵁ (i ⁻¹ᵁ (i.opensRange.ι ''ᵁ U)))) at hi
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
    inf_eq_right.mpr (i.opensRange.ι_image_le U)] at hi
  exact hi

end FLT.Mazur.FCurve
