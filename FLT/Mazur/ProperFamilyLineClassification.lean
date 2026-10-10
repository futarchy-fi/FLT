/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyAtlasRecovery

/-!
# Classification of original test-family direct-image lines

The actual proper base-change mate and cartesian dual atlas classify retained
lines on an unrestricted test base. The relation preserves the original
source and inclusion, before normalization by the mate.
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

local notation "M" => Functor.obj (pushforward f) L
local notation "hM" => properLinePushforward_locallyFiniteFree f L hL hV
local notation "N" => Functor.obj (pushforward q) (Functor.obj (pullback p) L)
local notation "e" => properLineArbitraryBaseChangeIso h L hL hV

/-- The actual original atlas morphisms over the specified test-base map. -/
abbrev TestMorphism := {a : T ⟶ space M hM // a ≫ projection M hM = g}

/-- Normalization reflects exactly the original retained-source relation. -/
lemma normalizedLine_rel_iff (a b : Line N) :
    (lineSetoid _).r (normalizedLine h L hL hV a) (normalizedLine h L hL hV b) ↔
      (lineSetoid N).r a b := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, (cancel_mono (e).inv).mp ?_⟩
    exact (Category.assoc _ _ _).trans hi
  · exact changeAmbient_respects (e).symm a b

/-- The original family atlas map detects original inclusion-preserving source isomorphisms. -/
theorem morphism_eq_iff (a b : Line N) :
    morphism h L hL hV a = morphism h L hL hV b ↔ (lineSetoid N).r a b := by
  have he : morphism h L hL hV a = morphism h L hL hV b ↔
      toSection _ ((hM).pullback g) (normalizedLine h L hL hV a) =
        toSection _ ((hM).pullback g) (normalizedLine h L hL hV b) := by
    constructor
    · intro hab
      apply (DualAtlasUniversalLine.morphismSectionEquiv M hM g).symm.injective
      exact Subtype.ext hab
    · intro hab
      exact congrArg (fun s : Section _ ((hM).pullback g) ↦
        s.val ≫ DualAtlasBaseChangeCharts.map g M hM) hab
  exact he.trans ((toSection_eq_iff _ _ _ _).trans (normalizedLine_rel_iff h L hL hV a b))

/-- Construct an original direct-image line from any actual morphism to the original atlas. -/
def lineOfMorphism (a : TestMorphism L hL hV (g := g)) : Line N :=
  (fromSection _ ((hM).pullback g)
    (DualAtlasUniversalLine.morphismSectionEquiv M hM g a)).changeAmbient (e)

/-- The constructed original line recovers the independently specified scheme morphism. -/
lemma morphism_lineOfMorphism (a : TestMorphism L hL hV (g := g)) :
    morphism h L hL hV (lineOfMorphism h L hL hV a) = a.val := by
  have hr : (lineSetoid _).r
      (normalizedLine h L hL hV (lineOfMorphism h L hL hV a))
      (fromSection _ ((hM).pullback g)
        (DualAtlasUniversalLine.morphismSectionEquiv M hM g a)) := by
    refine ⟨Iso.refl _, ?_⟩
    simp only [normalizedLine, lineOfMorphism, Line.changeAmbient, Iso.refl_hom,
      Iso.symm_hom, Category.id_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  unfold morphism DualAtlasUniversalLine.lineMorphism
  rw [(toSection_eq_iff _ _ _ _).mpr hr, toSection_fromSection]
  exact DualAtlasUniversalLine.sectionOfMorphism_map M hM g a.val a.property

/-- Every original atlas morphism is obtained from an original test-family line. -/
theorem morphism_surjective :
    Function.Surjective (fun b : Line N ↦
      (⟨morphism h L hL hV b, morphism_projection h L hL hV b⟩ :
        TestMorphism L hL hV (g := g))) :=
  fun a ↦ ⟨lineOfMorphism h L hL hV a, Subtype.ext (morphism_lineOfMorphism h L hL hV a)⟩

end FLT.Mazur.ProperFamilyAtlas
