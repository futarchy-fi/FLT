/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeFrameEquationSplitting

/-!
# The full scalar comparison as an equation on the original source

Over an independent coefficient pair, the actual relation comparison is
the equalizer imposing the second endpoint on the full first-source pullback.
No comparison coverage or equality of endpoint ranks is required.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelationComparisonEquation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A S B : Scheme.{0}} (p q : D ⟶ A) (f : A ⟶ S)
  (c : D ⟶ pullback f f) (hc₁ : c ≫ pullback.fst f f = p)
  (hc₂ : c ≫ pullback.snd f f = q) (t : B ⟶ pullback f f)
local notation "x" => t ≫ pullback.fst f f
local notation "y" => t ≫ pullback.snd f f
local notation "u" => pullback.fst p x ≫ q
local notation "v" => pullback.snd p x ≫ y

/-- Forget the second endpoint equation while retaining the whole original arrow. -/
def toSource : pullback c t ⟶ pullback p x :=
  pullback.lift (pullback.fst c t) (pullback.snd c t) (by
    rw [← hc₁, ← Category.assoc, pullback.condition, Category.assoc])

/-- The first-source comparison retains the original relation coordinate. -/
@[reassoc] theorem toSource_fst :
    toSource p f c hc₁ t ≫ pullback.fst p x = pullback.fst c t :=
  pullback.lift_fst _ _ _

/-- The first-source comparison retains the complete coefficient morphism. -/
@[reassoc] theorem toSource_snd :
    toSource p f c hc₁ t ≫ pullback.snd p x = pullback.snd c t :=
  pullback.lift_snd _ _ _

/-- Actual comparison arrows satisfy the exact second endpoint equation. -/
def toEquation : pullback c t ⟶ equalizer u v :=
  equalizer.lift (toSource p f c hc₁ t) (by
    rw [toSource_fst_assoc, toSource_snd_assoc, ← hc₂, ← Category.assoc,
      pullback.condition, Category.assoc])

/-- The equation map retains the whole first-source pullback coordinate. -/
@[reassoc] theorem toEquation_ι :
    toEquation p q f c hc₁ hc₂ t ≫ equalizer.ι u v = toSource p f c hc₁ t :=
  equalizer.lift_ι _ _

/-- A solution of the full second endpoint equation is an actual original comparison arrow. -/
def fromEquation : equalizer u v ⟶ pullback c t :=
  pullback.lift (equalizer.ι u v ≫ pullback.fst p x)
    (equalizer.ι u v ≫ pullback.snd p x) (by
      apply pullback.hom_ext
      · simp only [Category.assoc, hc₁]
        rw [pullback.condition]
      · simp only [Category.assoc, hc₂]
        exact equalizer.condition u v)

/-- The recovered comparison arrow keeps its original relation coordinate. -/
@[reassoc] theorem fromEquation_fst :
    fromEquation p q f c hc₁ hc₂ t ≫ pullback.fst c t =
      equalizer.ι u v ≫ pullback.fst p x := pullback.lift_fst _ _ _

/-- The recovered comparison arrow keeps its whole coefficient coordinate. -/
@[reassoc] theorem fromEquation_snd :
    fromEquation p q f c hc₁ hc₂ t ≫ pullback.snd c t =
      equalizer.ι u v ≫ pullback.snd p x := pullback.lift_snd _ _ _

attribute [local irreducible] toSource toEquation fromEquation

/-- The actual comparison is the full second-endpoint equation, over the unchanged test. -/
def iso : pullback c t ≅ equalizer u v where
  hom := toEquation p q f c hc₁ hc₂ t
  inv := fromEquation p q f c hc₁ hc₂ t
  hom_inv_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, fromEquation_fst, toEquation_ι_assoc, toSource_fst,
        Category.id_comp]
    · rw [Category.assoc, fromEquation_snd, toEquation_ι_assoc, toSource_snd,
        Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (equalizer.ι u v)).mp
    rw [Category.assoc, toEquation_ι, Category.id_comp]
    apply pullback.hom_ext
    · rw [Category.assoc, toSource_fst, fromEquation_fst]
    · rw [Category.assoc, toSource_snd, fromEquation_snd]

/-- The exact comparison isomorphism is over the full original coefficient scheme. -/
@[reassoc] theorem iso_projection :
    (iso p q f c hc₁ hc₂ t).hom ≫ equalizer.ι u v ≫ pullback.snd p x =
      pullback.snd c t := by
  change toEquation p q f c hc₁ hc₂ t ≫ _ ≫ _ = _
  rw [toEquation_ι_assoc, toSource_snd]

end FLT.Mazur.RelationComparisonEquation
