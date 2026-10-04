/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineSectionTwistSystem

/-!
# Open restriction of the actual section-twist system

The tensor restriction isomorphisms identify the restricted sequence with
the sequence formed from the restricted coefficient, line, and section.
The comparison commutes with every transition, not just successors.
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

variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
  (M : X.Modules) {L : X.Modules}

/-- The section on the restricted line, formed by ordinary restriction. -/
def restrictedSection (s : Γ(L, ⊤)) : Γ(L.restrict j, ⊤) :=
  L.presheaf.map (homOfLE (show j ''ᵁ ⊤ ≤ ⊤ from le_top)).op s

/-- Open restriction commutes with natural tensor powers. -/
def restrictedPowerIso (L : X.Modules) : ∀ n : ℕ,
    (tensorPower L n).restrict j ≅ tensorPower (L.restrict j) n
  | 0 => restrictUnitIso j
  | n + 1 => restrictIso L (tensorPower L n) j ≪≫
      congr (Iso.refl _) (restrictedPowerIso L n)

/-- The power comparison carries multiplication by the actual restricted section. -/
lemma restrictedPowerIso_step (s : Γ(L, ⊤)) (n : ℕ) :
    (restrictFunctor j).map (powerStep s n) ≫ (restrictedPowerIso j L (n + 1)).hom =
      (restrictedPowerIso j L n).hom ≫ powerStep (restrictedSection j s) n := by
  ext U t
  change Γ(tensorPower L n, j ''ᵁ U) at t
  change (restrictedPowerIso j L (n + 1)).hom.app U
    ((powerStep s n).app (j ''ᵁ U) t) =
      (powerStep (restrictedSection j s) n).app U ((restrictedPowerIso j L n).hom.app U t)
  rw [powerStep_app, powerStep_app]
  change (map (𝟙 (L.restrict j)) (restrictedPowerIso j L n).hom).app U
    ((restrictIso L (tensorPower L n) j).hom.app U
      (((tensor L (tensorPower L n)).restrictAppIso j U).inv
        (pure L (tensorPower L n) (j ''ᵁ U) _ t))) = _
  rw [restrictIso_hom_pure, map_pure]
  congr 1
  change L.presheaf.map (homOfLE (show j ''ᵁ U ≤ ⊤ from le_top)).op s =
    L.presheaf.map _ (L.presheaf.map _ s)
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Restriction of each coefficient twist is the corresponding restricted twist. -/
def restrictedTwistIso (n : ℕ) :
    (tensor M (tensorPower L n)).restrict j ≅
      tensor (M.restrict j) (tensorPower (L.restrict j) n) :=
  restrictIso M (tensorPower L n) j ≪≫ congr (Iso.refl _) (restrictedPowerIso j L n)

/-- The coefficient-twist comparison commutes with successor transitions. -/
lemma restrictedTwistIso_step (s : Γ(L, ⊤)) (n : ℕ) :
    (restrictFunctor j).map (step M s n) ≫ (restrictedTwistIso j M (L := L) (n + 1)).hom =
      (restrictedTwistIso j M (L := L) n).hom ≫
        step (M.restrict j) (restrictedSection j s) n := by
  dsimp only [step, restrictedTwistIso, Iso.trans_hom, ModuleSheafTensor.congr, Iso.refl_hom]
  rw [← Category.assoc, restrict_map]
  simp only [Category.assoc]
  rw [← map_comp, ← map_comp]
  congr 1
  simp only [Category.comp_id]
  exact congrArg (map (𝟙 (M.restrict j))) (restrictedPowerIso_step j s n)

/-- The entire actual twist system commutes with open restriction. -/
def restrictionSystemIso (s : Γ(L, ⊤)) :
    system M s ⋙ restrictFunctor j ≅ system (M.restrict j) (restrictedSection j s) := by
  let a : system M s ⋙ restrictFunctor j ⟶
      system (M.restrict j) (restrictedSection j s) :=
    NatTrans.ofSequence (fun n ↦ (restrictedTwistIso j M n).hom) (by
      intro n
      change (restrictFunctor j).map ((system M s).map _) ≫ _ = _
      rw [system_map_succ, system_map_succ]
      exact restrictedTwistIso_step j M s n)
  have : ∀ n, IsIso (a.app n) := fun _ ↦ inferInstanceAs (IsIso (restrictedTwistIso j M _).hom)
  have : IsIso a := NatIso.isIso_of_isIso_app a
  exact asIso a

end FLT.Mazur.FCurve.LineSectionTwistSystem
