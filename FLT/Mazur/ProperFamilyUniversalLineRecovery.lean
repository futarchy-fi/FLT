/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyAtlasCartesian
public import FLT.Mazur.ProperUniversalDirectImagePasting
public import FLT.Mazur.DirectImageBaseChangeNormalizedPasting

/-!
# Recovery of the actual universal direct-image line on the original family

Pull the universal line through the actual second mate and normalize its
coefficient sheaf on the independently specified test total space. The
result recovers the original retained source and its original inclusion.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.ProperFamilyAtlas
open FCurve LineSectionBaseChange DualAtlasLineQuotient LocallyFreeDualProjectiveAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
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
local notation "a" => morphism h L hL hV b

/-- Normalize the pulled universal coefficient to the original test-family coefficient. -/
def coefficientIso :
    (pullback (familyMap h L hL hV b)).obj
        ((pullback (Limits.pullback.fst f π)).obj L) ≅ (pullback p).obj L :=
  (SheafPullbackPathComparison.comparison (familyMap h L hL hV b)
    (Limits.pullback.fst f π) p (familyMap_fst h L hL hV b)).app L

/-- The actual universal direct-image line pulled to the original test family. -/
@[irreducible] def recoveredLine : Line ((pushforward q).obj ((pullback p).obj L)) :=
  (ProperUniversalDirectImage.iteratedLine f L hL hV a (familyMap h L hL hV b) q
    (familyMap_isPullback h L hL hV b)).changeAmbient
      ((pushforward q).mapIso (coefficientIso h L hL hV b))

/-- The original retained test-family source is recovered from the pulled universal line. -/
@[irreducible] def recoveryIso : (recoveredLine h L hL hV b).source ≅ b.source := by
  unfold recoveredLine ProperUniversalDirectImage.iteratedLine ProperUniversalDirectImage.line
  exact sourceIso h L hL hV b

/-- The recovery isomorphism commutes with the original test-family inclusion. -/
lemma recoveryIso_inclusion :
    (recoveryIso h L hL hV b).hom ≫ b.inclusion =
      (recoveredLine h L hL hV b).inclusion := by
  unfold recoveryIso recoveredLine ProperUniversalDirectImage.iteratedLine
    ProperUniversalDirectImage.line
  simp only [Line.changeAmbient, Line.baseChange, Functor.map_comp, Functor.mapIso_hom,
    properLineIteratedBaseChangeIso_hom, properLineArbitraryBaseChangeIso_hom,
    coefficientIso, Iso.app_hom, Category.assoc]
  rw [DirectImageBaseChange.comparison_paste_normalized
    (Limits.pullback.fst f π) (Limits.pullback.snd f π) f π
    Limits.pullback.condition.symm (familyMap h L hL hV b) q a
    (familyMap_snd h L hL hV b).symm p g
    (familyMap_fst h L hL hV b) (morphism_projection h L hL hV b) h.w.symm]
  exact sourceIso_inclusion h L hL hV b

/-- Recovery is equality in the original line classification, with the actual source witness. -/
lemma recoveredLine_equivalent :
    (lineSetoid _).r (recoveredLine h L hL hV b) b :=
  ⟨recoveryIso h L hL hV b, recoveryIso_inclusion h L hL hV b⟩

end FLT.Mazur.ProperFamilyAtlas
