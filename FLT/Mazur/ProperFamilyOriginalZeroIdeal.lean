/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyOriginalSectionRecovery
public import FLT.Mazur.RelativeCartierOriginalSquare
public import FLT.Mazur.LineSectionZeroIdealPullback

/-!
# The full original zero ideal is the pulled universal ideal

Geometric recovery identifies every equation, including multiplicities, in
the original test-family zero ideal. The universal relative Cartier theorem
then supplies the unrestricted-base forward splitting criterion.
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
  [IsProper f] [Flat f] [GeometricallyIntegral f] (h : IsPullback p q f g)
  (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))
  (B : SchemePicard.LineBundle T) (s : Γ(twist q ((pullback p).obj L) B, ⊤))
  (hs : SplitLineAffineNeighborhood.LocallySplit
    (twistedSectionPushforwardEquiv q ((pullback p).obj L) B.property s))

local notation "b" => originalTwistLine q (Functor.obj (pullback p) L) B s hs

local notation "M" => Functor.obj (pushforward f) L
local notation "hM" => properLinePushforward_locallyFiniteFree f L hL hV
local notation "π" => projection M hM
local notation "p₀" => Limits.pullback.fst f π
local notation "q₀" => Limits.pullback.snd f π
local notation "a" => morphism h L hL hV b
local notation "r" => familyMap h L hL hV b
local notation "l" => ProperUniversalDirectImage.line f L hL hV
local notation "N" => Functor.obj (pullback p₀) L

include h hL hV hs

/-- The full original section ideal is comap of the original universal ideal. -/
lemma originalSection_zeroIdeal :
    lineSectionZeroIdeal (twist_rankOne q ((pullback p).obj L) (hL.pullback p) B) s =
      (ProperUniversalDirectImage.universalIdeal f L hL hV).comap r := by
  let u := ProperUniversalDirectImage.universalRelativeSection f L hL hV
  let hu := twist_rankOne q₀ N (hL.pullback p₀) u.val.baseLine
  have hU := ProperUniversalDirectImage.universalIdeal_relativeCartier f L hL hV
  have hi := relativeCartierIdealPullback_originalSquare
    (familyMap_isPullback h L hL hV b) _ hU
  have hJ := (relativeCartier_originalSquare
    (familyMap_isPullback h L hL hV b) _ hU).1
  unfold ProperUniversalDirectImage.universalIdeal at hi hJ
  change IsIso (idealModulePullbackHom (lineSectionZeroIdeal hu u.val.section_) r) at hi
  change EffectiveCartier ((lineSectionZeroIdeal hu u.val.section_).comap r) at hJ
  let _ := hi
  let _ := u.val.regular
  unfold ProperUniversalDirectImage.universalIdeal
  change _ = (lineSectionZeroIdeal hu u.val.section_).comap r
  exact (lineSectionZeroIdeal_eq_of_iso (hu.pullback r) _
    (originalSectionRecoveryIso h L hL hV B s hs) _ _
    (originalSectionRecoveryIso_section h L hL hV B s hs)).symm.trans
      (lineSectionZeroIdeal_pullGlobal r hu u.val.section_ hJ)

/-- Recovery preserves regularity of the original independently specified section. -/
theorem originalSection_regular :
    Mono (globalSectionHom _ s) := by
  let u := ProperUniversalDirectImage.universalRelativeSection f L hL hV
  let hu := twist_rankOne q₀ N (hL.pullback p₀) u.val.baseLine
  have hU := ProperUniversalDirectImage.universalIdeal_relativeCartier f L hL hV
  have hi := relativeCartierIdealPullback_originalSquare
    (familyMap_isPullback h L hL hV b) _ hU
  have hJ := (relativeCartier_originalSquare
    (familyMap_isPullback h L hL hV b) _ hU).1
  unfold ProperUniversalDirectImage.universalIdeal at hi hJ
  change IsIso (idealModulePullbackHom (lineSectionZeroIdeal hu u.val.section_) r) at hi
  change EffectiveCartier ((lineSectionZeroIdeal hu u.val.section_).comap r) at hJ
  let _ := hi
  let _ := u.val.regular
  let _ := pullGlobal_regular_of_zeroIdeal r hu u.val.section_ hJ
  have he := globalSectionHom_naturality _
    (originalSectionRecoveryIso h L hL hV B s hs).hom (pullGlobal r _ u.val.section_)
  rw [originalSectionRecoveryIso_section] at he
  rw [← he]
  infer_instance

/-- A locally split original section has a relative Cartier zero divisor over any test base. -/
theorem originalSection_relativeCartier :
    RelativeEffectiveCartier q
      (lineSectionZeroIdeal (twist_rankOne q ((pullback p).obj L) (hL.pullback p) B) s) := by
  rw [originalSection_zeroIdeal h L hL hV B s hs]
  exact relativeCartier_originalSquare (familyMap_isPullback h L hL hV b) _
    (ProperUniversalDirectImage.universalIdeal_relativeCartier f L hL hV)

end FLT.Mazur.ProperFamilyAtlas
