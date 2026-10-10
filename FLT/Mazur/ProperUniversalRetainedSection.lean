/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperUniversalCartierDivisor
public import FLT.Mazur.RetainedLineTwistedSection

/-!
# The actual universal Cartier section retains its line-section construction

Identify the original universal relative section and full ideal with the
intrinsic tensor section of its retained direct-image line. These equalities
keep the original universal source and coefficient on the total space.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.ProperUniversalDirectImage
open FCurve LineSectionBaseChange CartierAbel LocallyFreeDualProjectiveAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor twistedSectionPushforwardEquiv
private lemma section_heq_of_map {Y B : Scheme.{0}} (t : Y ⟶ B) (N : Y.Modules)
    {A C : SchemePicard.LineBundle B} (h : A = C)
    {s : Γ(twist t N A, ⊤)} {v : Γ(twist t N C, ⊤)}
    (he : HEq (twistedSectionPushforwardEquiv t N A.property s)
      (twistedSectionPushforwardEquiv t N C.property v)) : HEq s v := by
  subst C
  exact heq_of_eq ((twistedSectionPushforwardEquiv t N A.property).injective (eq_of_heq he))

private lemma zeroIdeal_eq_of_section_heq {Y B : Scheme.{0}} (t : Y ⟶ B) (N : Y.Modules)
    (hN : LocallyFreeRankOne N) {A C : SchemePicard.LineBundle B} (h : A = C)
    {s : Γ(twist t N A, ⊤)} {v : Γ(twist t N C, ⊤)} (he : HEq s v) :
    lineSectionZeroIdeal (twist_rankOne t N hN A) s =
      lineSectionZeroIdeal (twist_rankOne t N hN C) v := by
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

/-- The actual universal tensor section is the retained line's intrinsic tensor section. -/
lemma universalSection_retained :
    HEq (universalRelativeSection f L hL hV).val.section_
      (retainedLineSection q ((pullback p).obj L) (line f L hL hV)) := by
  apply section_heq_of_map q _ (universalRelativeSection_baseLine f L hL hV)
  exact (universalRelativeSection_map f L hL hV).trans
    (heq_of_eq (retainedLineSection_map q _ (line f L hL hV)).symm)

/-- The original universal ideal is the full zero ideal of its retained tensor section. -/
lemma universalIdeal_retained :
    universalIdeal f L hL hV =
      lineSectionZeroIdeal ((hL.pullback p).tensor
        ((line f L hL hV).rankOne.dual.pullback q))
        (retainedLineSection q ((pullback p).obj L) (line f L hL hV)) := by
  unfold universalIdeal
  exact zeroIdeal_eq_of_section_heq q _ (hL.pullback p)
    (universalRelativeSection_baseLine f L hL hV) (universalSection_retained f L hL hV)

end FLT.Mazur.ProperUniversalDirectImage
