/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorInvertibleSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.CategoryTheory.Limits.Preorder

/-!
# Pullback of line bundles

The actual module-sheaf pullback preserves the structure module and local
rank one. Restriction compatibility is obtained from composition of pullbacks.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace FLT.Mazur.FCurve

variable {X Y Z : Scheme.{u}}

/-- Pullback carries the structure module to the structure module. -/
def modulePullbackUnitIso (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (structureModule Y) ≅ structureModule X := by
  let F := TopologicalSpace.Opens.map f.base
  let : F.Final := by
    let : (Functor.fromPUnit.{0} (⊤ : Y.Opens)).Final :=
      Functor.final_fromPUnit_of_isTerminal CategoryTheory.Limits.isTerminalTop
    let : (Functor.fromPUnit.{0} (⊤ : X.Opens)).Final :=
      Functor.final_fromPUnit_of_isTerminal CategoryTheory.Limits.isTerminalTop
    let : (Functor.fromPUnit.{0} (⊤ : Y.Opens) ⋙ F).Final :=
      Functor.final_of_natIso (F := Functor.fromPUnit.{0} (⊤ : X.Opens))
        (Discrete.natIso (fun _ ↦ eqToIso (by ext; simp [F])))
    exact Functor.final_of_final_comp (Functor.fromPUnit.{0} (⊤ : Y.Opens)) F
  let e := SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom
  let : IsIso e := SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal _
  exact asIso e

/-- Compatibility with restriction in a commuting square of open immersions. -/
def modulePullbackRestrictIso {W : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ W)
    (i : Z ⟶ X) (j : W ⟶ Y) [IsOpenImmersion i] [IsOpenImmersion j]
    (h : i ≫ f = g ≫ j) (M : Y.Modules) :
    ((Scheme.Modules.pullback f).obj M).restrict i ≅
      (Scheme.Modules.pullback g).obj (M.restrict j) :=
  (Scheme.Modules.restrictFunctorIsoPullback i).app _ ≪≫
    (Scheme.Modules.pullbackComp i f).app M ≪≫
    (Scheme.Modules.pullbackCongr h).app M ≪≫
    ((Scheme.Modules.pullbackComp g j).app M).symm ≪≫
    (Scheme.Modules.pullback g).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback j).app M).symm

/-- Restricting a pullback to the inverse image of an open is pullback of the restriction. -/
def modulePullbackOpenIso (f : X ⟶ Y) (U : Y.Opens) (M : Y.Modules) :
    ((Scheme.Modules.pullback f).obj M).restrict (f ⁻¹ᵁ U).ι ≅
      (Scheme.Modules.pullback (f ∣_ U)).obj (M.restrict U.ι) :=
  modulePullbackRestrictIso f (f ∣_ U) (f ⁻¹ᵁ U).ι U.ι
    (morphismRestrict_ι f U).symm M

/-- Pull a local trivialization back to the inverse-image open. -/
def modulePullbackTrivialization (f : X ⟶ Y) {M : Y.Modules} {U : Y.Opens}
    (e : M.restrict U.ι ≅ structureModule U.toScheme) :
    ((Scheme.Modules.pullback f).obj M).restrict (f ⁻¹ᵁ U).ι ≅
      structureModule (f ⁻¹ᵁ U).toScheme :=
  modulePullbackOpenIso f U M ≪≫ (Scheme.Modules.pullback (f ∣_ U)).mapIso e ≪≫
    modulePullbackUnitIso (f ∣_ U)

/-- Pullback along any scheme morphism preserves locally free rank-one module sheaves. -/
theorem LocallyFreeRankOne.pullback {M : Y.Modules} (hM : LocallyFreeRankOne M)
    (f : X ⟶ Y) : LocallyFreeRankOne ((Scheme.Modules.pullback f).obj M) := by
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := hM (f x)
  exact ⟨f ⁻¹ᵁ U, hx, ⟨modulePullbackTrivialization f e⟩⟩

/-- Restriction along an open immersion preserves locally free rank one. -/
theorem LocallyFreeRankOne.restrict {M : Y.Modules} (hM : LocallyFreeRankOne M)
    (f : X ⟶ Y) [IsOpenImmersion f] : LocallyFreeRankOne (M.restrict f) :=
  (hM.pullback f).of_iso ((Scheme.Modules.restrictFunctorIsoPullback f).app M).symm

end FLT.Mazur.FCurve
