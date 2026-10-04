/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleLineTensorExact
public import FLT.Mazur.ModuleHomIsomorphismOpen
public import FLT.Mazur.ModuleTensorPowerSection
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# The transition system for multiplication by a line section

The terms are the actual sheaf tensors `M ⊗ Lⁿ`. Successor maps insert the
given section in the next line factor. No cohomological vanishing is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.FCurve.LineSectionTwistSystem

open ModuleSheafTensor ModuleLineBundleTensorPullback

variable {X Y : Scheme.{u}} {L : X.Modules}

/-- Multiplication by a section on a tensor power, including degree zero. -/
def powerStep (s : Γ(L, ⊤)) (n : ℕ) : tensorPower L n ⟶ tensorPower L (n + 1) :=
  (leftUnitor _).inv ≫ ModuleSheafTensor.map (globalSectionHom L s) (𝟙 _)

/-- Multiplication by a section on an arbitrary coefficient twist. -/
def step (M : X.Modules) (s : Γ(L, ⊤)) (n : ℕ) :
    tensor M (tensorPower L n) ⟶ tensor M (tensorPower L (n + 1)) :=
  ModuleSheafTensor.map (𝟙 M) (powerStep s n)

/-- The complete directed system, with composition supplied by the sequence functor. -/
def system (M : X.Modules) (s : Γ(L, ⊤)) : ℕ ⥤ X.Modules :=
  Functor.ofSequence (step M s)

@[simp]
lemma system_obj (M : X.Modules) (s : Γ(L, ⊤)) (n : ℕ) :
    (system M s).obj n = tensor M (tensorPower L n) := rfl

@[simp]
lemma system_map_succ (M : X.Modules) (s : Γ(L, ⊤)) (n : ℕ) :
    (system M s).map (homOfLE (Nat.le_add_right n 1)) = step M s n :=
  Functor.ofSequence_map_homOfLE_succ _ n

/-- On actual local sections the transition inserts the restriction of the section. -/
lemma powerStep_app (s : Γ(L, ⊤)) (n : ℕ) (U : X.Opens)
    (t : Γ(tensorPower L n, U)) :
    (powerStep s n).app U t = pure L (tensorPower L n) U
      (L.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s) t := by
  have h : (leftUnitor (tensorPower L n)).inv.app U t =
      pure (structureModule X) (tensorPower L n) U (1 : Γ(X, U)) t := by
    apply (ConcreteCategory.bijective_of_isIso ((leftUnitor (tensorPower L n)).hom.app U)).injective
    simp only [← ConcreteCategory.comp_apply, ← Hom.comp_app, Iso.inv_hom_id,
      Hom.id_app, ConcreteCategory.id_apply]
    exact (leftUnitor_pure (tensorPower L n) U (1 : Γ(X, U)) t).trans
      (one_smul Γ(X, U) t) |>.symm
  simp only [powerStep, Hom.comp_app, ConcreteCategory.comp_apply, h]
  exact (ModuleSheafTensor.map_pure (globalSectionHom L s) (𝟙 (tensorPower L n))
    U (1 : Γ(X, U)) t).trans (by
      simp only [Hom.id_app, ConcreteCategory.id_apply]
      change pure L (tensorPower L n) U ((1 : Γ(X, U)) •
        L.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s) t = _
      rw [one_smul])

/-- The transition on a pure coefficient section is ordinary section multiplication. -/
lemma step_pure (M : X.Modules) (s : Γ(L, ⊤)) (n : ℕ) (U : X.Opens)
    (m : Γ(M, U)) (t : Γ(tensorPower L n, U)) :
    (step M s n).app U (pure M (tensorPower L n) U m t) =
      pure M (tensorPower L (n + 1)) U m
        (pure L (tensorPower L n) U
          (L.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s) t) := by
  simp only [step, ModuleSheafTensor.map_pure, Hom.id_app, ConcreteCategory.id_apply, powerStep_app]

/-- Tensor restriction is natural in both coefficient maps. -/
lemma restrict_map {M N P Q : X.Modules} (j : Y ⟶ X) [IsOpenImmersion j]
    (a : M ⟶ N) (b : P ⟶ Q) :
    (restrictFunctor j).map (ModuleSheafTensor.map a b) ≫ (restrictIso N Q j).hom =
      (restrictIso M P j).hom ≫
        ModuleSheafTensor.map ((restrictFunctor j).map a) ((restrictFunctor j).map b) := by
  apply restrict_hom_ext j
  intro U m p
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, restrictIso_hom_pure,
    ModuleSheafTensor.map_pure]
  change (restrictIso N Q j).hom.app U
    (((tensor N Q).restrictAppIso j U).inv
      ((ModuleSheafTensor.map a b).app (j ''ᵁ U) (pure M P (j ''ᵁ U) m p))) = _
  rw [ModuleSheafTensor.map_pure, restrictIso_hom_pure]
  rfl

/-- Tensoring two invertible maps is invertible. -/
lemma map_isIso {M N P Q : X.Modules} (a : M ⟶ N) (b : P ⟶ Q)
    [IsIso a] [IsIso b] : IsIso (ModuleSheafTensor.map a b) :=
  inferInstanceAs (IsIso (congr (asIso a) (asIso b)).hom)

/-- Invertibility after restriction is preserved by the sheaf tensor. -/
lemma restrict_map_isIso {M N P Q : X.Modules} (j : Y ⟶ X) [IsOpenImmersion j]
    (a : M ⟶ N) (b : P ⟶ Q)
    [IsIso ((restrictFunctor j).map a)] [IsIso ((restrictFunctor j).map b)] :
    IsIso ((restrictFunctor j).map (ModuleSheafTensor.map a b)) := by
  have := map_isIso ((restrictFunctor j).map a) ((restrictFunctor j).map b)
  have he := restrict_map j a b
  have : IsIso ((restrictFunctor j).map (ModuleSheafTensor.map a b) ≫
      (restrictIso N Q j).hom) := by rw [he]; infer_instance
  exact IsIso.of_isIso_comp_right _ (restrictIso N Q j).hom

/-- Every successor becomes invertible on the generator open of the section. -/
theorem step_isIso_on_generatorOpen (M : X.Modules) (s : Γ(L, ⊤)) (n : ℕ) :
    IsIso ((restrictFunctor (sectionGeneratorOpen L s).ι).map (step M s n)) := by
  let j := (sectionGeneratorOpen L s).ι
  have : IsIso ((restrictFunctor j).map (globalSectionHom L s)) :=
    moduleHomIsoOpen_isIso (globalSectionHom L s)
  have := restrict_map_isIso j (globalSectionHom L s) (𝟙 (tensorPower L n))
  have : IsIso ((restrictFunctor j).map (powerStep s n)) := by
    dsimp only [powerStep]
    rw [Functor.map_comp]
    infer_instance
  exact restrict_map_isIso j (𝟙 M) (powerStep s n)

end FLT.Mazur.FCurve.LineSectionTwistSystem
