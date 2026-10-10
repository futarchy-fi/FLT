/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalFamilySectionComposition
public import FLT.Mazur.ProperFamilyIteratedSectionOrbits

/-!
# The prescribed composition on original family sections

The original twisting-line comparison is exactly the sheaf pullback composition.
It preserves the directly pulled sections on the original test families.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.CartierAbel
open FCurve ProperFamilyTests LineSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor originalFamilyTwistIso
attribute [local irreducible] originalFamilyPullSection
variable {X S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  {f : X ⟶ S} [IsProper f] [Flat f] [GeometricallyIntegral f]
  (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))
  {A B C : Family f}

/-- The prescribed composition carries the actual iterated family section. -/
lemma familySectionMap_comp_section (u : A ⟶ B) (v : B ⟶ C)
    (t : RelativeSection C.snd ((pullback C.fst).obj L) (hL.pullback C.fst)) :
    (ModuleSheafTensor.map (𝟙 ((pullback A.fst).obj L))
      ((pullback A.snd).map ((pullbackComp u.base v.base).hom.app t.val.baseLine.val))).app ⊤
      (familySectionMap L hL hV u (familySectionMap L hL hV v t)).val.section_ =
        (familySectionMap L hL hV (u ≫ v) t).val.section_ := by
  dsimp only [familySectionMap, familySectionPullback, familyPulledTwistedSection]
  exact originalFamilyPullSection_comp v.base u.base v.total u.total v.fst v.snd u.fst u.snd
    (u ≫ v).fst (u ≫ v).snd L t.val.baseLine t.val.section_

/-- Every original section-preserving composite comparison is the prescribed one. -/
lemma familySectionMap_comp_iso_unique (u : A ⟶ B) (v : B ⟶ C)
    (t : RelativeSection C.snd ((pullback C.fst).obj L) (hL.pullback C.fst))
    (e : (familySectionMap L hL hV u (familySectionMap L hL hV v t)).val.baseLine.val ≅
      (familySectionMap L hL hV (u ≫ v) t).val.baseLine.val)
    (he : (ModuleSheafTensor.map (𝟙 ((pullback A.fst).obj L))
      ((pullback A.snd).map e.hom)).app ⊤
      (familySectionMap L hL hV u (familySectionMap L hL hV v t)).val.section_ =
        (familySectionMap L hL hV (u ≫ v) t).val.section_) :
    e = (pullbackComp u.base v.base).app t.val.baseLine.val :=
  familyOriginalTwistIso_unique L hL hV _ _ e _ he
    (familySectionMap_comp_section L hL hV u v t)

end FLT.Mazur.CartierAbel
