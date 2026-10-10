/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilySectionPullback
public import FLT.Mazur.ProperUniversalTensorIdentification
public import FLT.Mazur.ModuleSectionMap

/-!
# Recovery of the original universal relative tensor section

Geometric pullback of the original universal section recovers the original
retained test-family section through an actual tensor-line isomorphism.
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

/-- Geometric recovery includes the original universal line and original test source. -/
@[irreducible] def universalSectionRecoveryIso :
    (pullback r).obj (twist q₀ N
      (ProperUniversalDirectImage.universalRelativeSection f L hL hV).val.baseLine) ≅
    ModuleSheafTensor.tensor ((pullback p).obj L)
      ((pullback q).obj (moduleSheafDual b.source)) :=
  (pullback r).mapIso (ProperUniversalDirectImage.universalTensorIso f L hL hV) ≪≫
    sectionPullbackIso h L hL hV b ≪≫
      (ModuleSheafTensor.congr (Iso.refl ((pullback p).obj L))
        ((pullback q).mapIso (recoveredTwistIso h L hL hV b))).symm

/-- The actual pulled universal section is the original retained test-family section. -/
lemma universalSectionRecoveryIso_section :
    (universalSectionRecoveryIso h L hL hV b).hom.app ⊤
        (pullGlobal r _
          (ProperUniversalDirectImage.universalRelativeSection f L hL hV).val.section_) =
      retainedLineSection q ((pullback p).obj L) b := by
  unfold universalSectionRecoveryIso
  rw [Iso.trans_hom, Iso.trans_hom, Hom.comp_app, ConcreteCategory.comp_apply,
    Functor.mapIso_hom, pullGlobal_naturality,
    ProperUniversalDirectImage.universalTensorIso_section,
    Hom.comp_app, ConcreteCategory.comp_apply, sectionPullbackIso_section]
  exact sectionIso_inv_of_eq
    (ModuleSheafTensor.congr (Iso.refl ((pullback p).obj L))
      ((pullback q).mapIso (recoveredTwistIso h L hL hV b))) ⊤ _ _
    (recoveredSection_eq h L hL hV b)

end FLT.Mazur.ProperFamilyAtlas
