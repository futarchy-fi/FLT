/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperUniversalRetainedSection

/-!
# Identification of the original universal tensor line

The independently constructed universal relative section is carried to its
retained tensor presentation by the proved equality of original base lines.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.ProperUniversalDirectImage
open FCurve LineSectionBaseChange CartierAbel LocallyFreeDualProjectiveAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor twistedSectionPushforwardEquiv
private lemma section_eq_of_heq {Y B : Scheme.{0}} (t : Y ⟶ B) (N : Y.Modules)
    {A C : SchemePicard.LineBundle B} (h : A = C)
    {s : Γ(twist t N A, ⊤)} {v : Γ(twist t N C, ⊤)} (he : HEq s v) :
    (eqToIso (congrArg (twist t N) h)).hom.app ⊤ s = v := by
  subst C
  cases he
  rfl

variable {X S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (f : X ⟶ S) [IsProper f] [Flat f] [GeometricallyIntegral f]
  (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))

local notation "M" => Functor.obj (pushforward f) L
local notation "hM" => properLinePushforward_locallyFiniteFree f L hL hV
local notation "A" => space M hM
local notation "π" => projection M hM
local notation "p" => Limits.pullback.fst f π
local notation "q" => Limits.pullback.snd f π

/-- The original universal coefficient line identifies with its intrinsic retained tensor. -/
@[irreducible] def universalTensorIso :
    twist q ((pullback p).obj L) (universalRelativeSection f L hL hV).val.baseLine ≅
      ModuleSheafTensor.tensor ((pullback p).obj L)
        ((pullback q).obj (moduleSheafDual (line f L hL hV).source)) :=
  eqToIso (congrArg (twist q ((pullback p).obj L))
    (universalRelativeSection_baseLine f L hL hV))

/-- The coefficient identification retains the original universal tensor section. -/
lemma universalTensorIso_section :
    (universalTensorIso f L hL hV).hom.app ⊤
        (universalRelativeSection f L hL hV).val.section_ =
      retainedLineSection q ((pullback p).obj L) (line f L hL hV) := by
  unfold universalTensorIso
  exact section_eq_of_heq q _ (universalRelativeSection_baseLine f L hL hV)
    (universalSection_retained f L hL hV)

end FLT.Mazur.ProperUniversalDirectImage
