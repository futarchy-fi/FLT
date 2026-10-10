/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyTwistedRecovery
public import FLT.Mazur.RetainedLineSectionPullbackIso
public import FLT.Mazur.TwistedSectionCoefficientNaturality

/-!
# Geometric recovery of the proper family's retained tensor section

The actual universal tensor section is pulled along the original family map.
Tensor, square, dual and coefficient comparisons identify its value with
that of the recovered line on the independently specified test family.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.ProperFamilyAtlas
open FCurve CartierAbel LineSectionBaseChange DualAtlasLineQuotient LocallyFreeDualProjectiveAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor
attribute [local irreducible] LocallyFreeDualProjectiveAtlas.space
attribute [local irreducible] LocallyFreeDualProjectiveAtlas.projection
variable {P X T S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  [IsProper f] [Flat f] (h : IsPullback p q f g)
  (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))
  (b : Line ((pushforward q).obj ((pullback p).obj L)))

local notation "M" => Functor.obj (pushforward f) L
local notation "hM" => properLinePushforward_locallyFiniteFree f L hL hV
local notation "π" => projection M hM
local notation "p₀" => Limits.pullback.fst f π
local notation "q₀" => Limits.pullback.snd f π
local notation "a" => morphism h L hL hV b
local notation "r" => familyMap h L hL hV b
local notation "l" => ProperUniversalDirectImage.line f L hL hV
local notation "N" => Functor.obj (pullback p₀) L

/-- The geometric tensor comparison includes the original coefficient path normalization. -/
@[irreducible] def sectionPullbackIso :
    (pullback r).obj (ModuleSheafTensor.tensor N
      ((pullback q₀).obj (moduleSheafDual (l).source))) ≅
    ModuleSheafTensor.tensor ((pullback p).obj L)
      ((pullback q).obj (moduleSheafDual (recoveredLine h L hL hV b).source)) := by
  unfold recoveredLine ProperUniversalDirectImage.iteratedLine
  exact retainedLinePullbackIso r q q₀ a (familyMap_snd h L hL hV b).symm N l ≪≫
    ModuleSheafTensor.congr (coefficientIso h L hL hV b) (Iso.refl _)

/-- Pulling the universal retained section recovers the actual normalized test section. -/
lemma sectionPullbackIso_section :
    (sectionPullbackIso h L hL hV b).hom.app ⊤
        (pullGlobal r _ (retainedLineSection q₀ N l)) =
      retainedLineSection q ((pullback p).obj L) (recoveredLine h L hL hV b) := by
  let e := properLineIteratedBaseChangeIso (IsPullback.of_hasPullback f π) L hL hV
    (familyMap_isPullback h L hL hV b)
  have he : e.hom = DirectImageBaseChange.comparison r q q₀ a
      (familyMap_snd h L hL hV b).symm N :=
    properLineIteratedBaseChangeIso_hom _ _ _ _ _
  have hp := retainedLinePullbackIso_section r q q₀ a
    (familyMap_snd h L hL hV b).symm N l e he
  unfold sectionPullbackIso
  dsimp only [id, Iso.trans_hom, Hom.comp_app, ConcreteCategory.comp_apply,
    ModuleSheafTensor.congr, Iso.refl_hom]
  unfold recoveredLine ProperUniversalDirectImage.iteratedLine
  exact (congrArg (fun s ↦ (ModuleSheafTensor.map
    (coefficientIso h L hL hV b).hom (𝟙 _)).app ⊤ s) hp).trans
      (retainedLineSection_coefficient q (coefficientIso h L hL hV b)
        (((l).baseChange a).changeAmbient e))

end FLT.Mazur.ProperFamilyAtlas
