/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TranslatedHilbertTestUnionLift

/-!
# Arbitrary test base change of the translated chart union

The union attached to a restricted original section is the actual pullback of
the original open union. No new finite-type hypothesis on the test is required.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {X : Scheme} (f : X ⟶ Spec (.of R))
  [Algebra.FiniteType ℤ R] [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  {ι : Type} (a : ι → TranslatedHilbertIndex f)
  {T U : Over (Spec (.of R))} (b : U ⟶ T) (s : (relativeFppfSheaf f).obj.obj (op T))

/-- The restricted union maps to the original union with both original coordinates. -/
theorem translatedHilbertTestUnion_baseChange_exists :
    ∃! q : translatedHilbertTestUnion f a U ((relativeFppfSheaf f).obj.map b.op s) ⟶
        translatedHilbertTestUnion f a T s,
      q ≫ translatedHilbertTestUnionι f a T s =
        translatedHilbertTestUnionι f a U ((relativeFppfSheaf f).obj.map b.op s) ≫ b ∧
      q ≫ translatedHilbertTestUnionToGlued f hL a T s =
        translatedHilbertTestUnionToGlued f hL a U ((relativeFppfSheaf f).obj.map b.op s) := by
  apply translatedHilbertTestUnion_lift f hL a
  rw [translatedHilbertTestUnion_class]
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

/-- The actual morphism of open unions induced by restricting the original section. -/
def translatedHilbertTestUnionBaseChange :
    translatedHilbertTestUnion f a U ((relativeFppfSheaf f).obj.map b.op s) ⟶
      translatedHilbertTestUnion f a T s :=
  (translatedHilbertTestUnion_baseChange_exists f hL a b s).choose

@[reassoc]
theorem translatedHilbertTestUnionBaseChange_ι :
    translatedHilbertTestUnionBaseChange f hL a b s ≫ translatedHilbertTestUnionι f a T s =
      translatedHilbertTestUnionι f a U ((relativeFppfSheaf f).obj.map b.op s) ≫ b :=
  (translatedHilbertTestUnion_baseChange_exists f hL a b s).choose_spec.1.1

@[reassoc]
theorem translatedHilbertTestUnionBaseChange_toGlued :
    translatedHilbertTestUnionBaseChange f hL a b s ≫
        translatedHilbertTestUnionToGlued f hL a T s =
      translatedHilbertTestUnionToGlued f hL a U ((relativeFppfSheaf f).obj.map b.op s) :=
  (translatedHilbertTestUnion_baseChange_exists f hL a b s).choose_spec.1.2

/-- The new union is the full relative pullback of the original open inclusion. -/
theorem translatedHilbertTestUnionBaseChange_isPullback :
    IsPullback (translatedHilbertTestUnionBaseChange f hL a b s)
      (translatedHilbertTestUnionι f a U ((relativeFppfSheaf f).obj.map b.op s))
      (translatedHilbertTestUnionι f a T s) b := by
  let lift (z : PullbackCone (translatedHilbertTestUnionι f a T s) b) :=
    translatedHilbertTestUnion_lift f hL a U ((relativeFppfSheaf f).obj.map b.op s)
      z.snd (z.fst ≫ translatedHilbertTestUnionToGlued f hL a T s) (by
        rw [translatedHilbertGluedPoint_natural, translatedHilbertTestUnion_class,
          ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, z.condition]
        simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply])
  have hl z : (lift z).choose ≫ translatedHilbertTestUnionBaseChange f hL a b s = z.fst := by
    apply (cancel_mono (translatedHilbertTestUnionι f a T s)).mp
    rw [Category.assoc, translatedHilbertTestUnionBaseChange_ι, ← Category.assoc,
      (lift z).choose_spec.1.1, z.condition]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (translatedHilbertTestUnionBaseChange_ι f hL a b s) (fun z ↦ (lift z).choose)
    hl (fun z ↦ (lift z).choose_spec.1.1) ?_)
  intro z q _ hq
  exact (cancel_mono
    (translatedHilbertTestUnionι f a U ((relativeFppfSheaf f).obj.map b.op s))).mp
      (hq.trans (lift z).choose_spec.1.1.symm)

end FLT.Mazur.HilbertChart
