/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyUniversalSectionRecovery
public import FLT.Mazur.RetainedLineOriginalTwist

/-!
# Recovery with the original independently specified twisting line

The classifying family map comes from the original section's locally split
direct-image map. Its pulled universal tensor section is identified with the
original section in its original tensor line, before passing to zero ideals.
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

/-- Recovery returns to the original twisting line by inverse canonical biduality. -/
@[irreducible] def originalSectionRecoveryIso :
    (pullback r).obj (twist q₀ N
      (ProperUniversalDirectImage.universalRelativeSection f L hL hV).val.baseLine) ≅
      twist q ((pullback p).obj L) B :=
  universalSectionRecoveryIso h L hL hV b ≪≫
    (ModuleSheafTensor.congr (Iso.refl ((pullback p).obj L))
      ((pullback q).mapIso (originalTwistIso q ((pullback p).obj L) B s hs))).symm

/-- The original section is the actual geometric pullback of the universal section. -/
lemma originalSectionRecoveryIso_section :
    (originalSectionRecoveryIso h L hL hV B s hs).hom.app ⊤
        (pullGlobal r _
          (ProperUniversalDirectImage.universalRelativeSection f L hL hV).val.section_) = s := by
  unfold originalSectionRecoveryIso
  rw [Iso.trans_hom, Hom.comp_app, ConcreteCategory.comp_apply,
    universalSectionRecoveryIso_section]
  exact sectionIso_inv_of_eq
    (ModuleSheafTensor.congr (Iso.refl ((pullback p).obj L))
      ((pullback q).mapIso (originalTwistIso q ((pullback p).obj L) B s hs))) ⊤ _ _
    (originalTwistLine_section q ((pullback p).obj L) B s hs)

end FLT.Mazur.ProperFamilyAtlas
