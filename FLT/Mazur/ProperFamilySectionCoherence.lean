/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalTwistSectionCoherence
public import FLT.Mazur.ProperFamilyPrescribedComposition

/-!
# Coherence on iterated original family representatives

The two extreme pentagon paths both carry the actual fourfold pulled section
to its original composite pullback. Threefold pullback has the same normalization.
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
  {A B C D E : Family f}

/-- Section transport along the prescribed composition is the actual composite pullback. -/
lemma familySectionMap_comp_action (u : A ⟶ B) (v : B ⟶ C)
    (t : RelativeSection C.snd ((pullback C.fst).obj L) (hL.pullback C.fst)) :
    originalTwistSectionMap A.snd ((pullback A.fst).obj L)
      ((pullbackComp u.base v.base).hom.app t.val.baseLine.val)
      (familySectionMap L hL hV u (familySectionMap L hL hV v t)).val.section_ =
      (familySectionMap L hL hV (u ≫ v) t).val.section_ :=
  familySectionMap_comp_section L hL hV u v t

/-- Three actual section pullbacks normalize by the prescribed original comparisons. -/
lemma familySectionMap_three_section (u : A ⟶ B) (v : B ⟶ C) (w : C ⟶ D)
    (t : RelativeSection D.snd ((pullback D.fst).obj L) (hL.pullback D.fst)) :
    originalTwistSectionMap A.snd ((pullback A.fst).obj L)
      ((pullbackComp u.base v.base).hom.app ((pullback w.base).obj t.val.baseLine.val) ≫
        (pullbackComp (u.base ≫ v.base) w.base).hom.app t.val.baseLine.val)
      (familySectionMap L hL hV u
        (familySectionMap L hL hV v (familySectionMap L hL hV w t))).val.section_ =
      (familySectionMap L hL hV ((u ≫ v) ≫ w) t).val.section_ := by
  rw [originalTwistSectionMap_comp]
  erw [familySectionMap_comp_action L hL hV u v (familySectionMap L hL hV w t)]
  exact familySectionMap_comp_action L hL hV (u ≫ v) w t

/-- Four actual original sections normalize along the left-associated pentagon path. -/
lemma familySectionMap_four_section (u : A ⟶ B) (v : B ⟶ C)
    (w : C ⟶ D) (z : D ⟶ E)
    (t : RelativeSection E.snd ((pullback E.fst).obj L) (hL.pullback E.fst)) :
    originalTwistSectionMap A.snd ((pullback A.fst).obj L)
      ((pullbackComp u.base v.base).hom.app
          ((pullback w.base).obj ((pullback z.base).obj t.val.baseLine.val)) ≫
        (pullbackComp (u.base ≫ v.base) w.base).hom.app
          ((pullback z.base).obj t.val.baseLine.val) ≫
        (pullbackComp ((u.base ≫ v.base) ≫ w.base) z.base).hom.app t.val.baseLine.val)
      (familySectionMap L hL hV u (familySectionMap L hL hV v
        (familySectionMap L hL hV w (familySectionMap L hL hV z t)))).val.section_ =
      (familySectionMap L hL hV (((u ≫ v) ≫ w) ≫ z) t).val.section_ := by
  rw [originalTwistSectionMap_comp]
  erw [familySectionMap_comp_action L hL hV u v
    (familySectionMap L hL hV w (familySectionMap L hL hV z t))]
  exact familySectionMap_three_section L hL hV (u ≫ v) w z t

/-- The other pentagon path has the same actual composite original section as endpoint. -/
lemma familySectionMap_pentagon_section (u : A ⟶ B) (v : B ⟶ C)
    (w : C ⟶ D) (z : D ⟶ E)
    (t : RelativeSection E.snd ((pullback E.fst).obj L) (hL.pullback E.fst)) :
    originalTwistSectionMap A.snd ((pullback A.fst).obj L)
      ((pullback u.base).map
          ((pullback v.base).map ((pullbackComp w.base z.base).hom.app t.val.baseLine.val)) ≫
        (pullback u.base).map
          ((pullbackComp v.base (w.base ≫ z.base)).hom.app t.val.baseLine.val) ≫
        (SheafPullbackPathComparison.comparison u.base (v.base ≫ (w.base ≫ z.base))
          (((u.base ≫ v.base) ≫ w.base) ≫ z.base)
          (by simp only [Category.assoc])).hom.app t.val.baseLine.val)
      (familySectionMap L hL hV u (familySectionMap L hL hV v
        (familySectionMap L hL hV w (familySectionMap L hL hV z t)))).val.section_ =
      (familySectionMap L hL hV (((u ≫ v) ≫ w) ≫ z) t).val.section_ := by
  rw [originalTwistSectionMap_pentagon]
  exact familySectionMap_four_section L hL hV u v w z t

end FLT.Mazur.CartierAbel
