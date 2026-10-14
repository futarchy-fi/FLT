/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationOpenSelectorTestCharts

/-!
# Coequalization of the full original relation by the glued projection

Compatibility is checked on actual scheme arrows, using the original open
cover and both independently lifted coordinates. No reducedness is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationOpenSelector
open RelativeRelationOrbit SchemeRelationRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] sourceOpen sourceChart
variable {S : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) [Etale q.left]
local notation "B" => Scheme.Opens.toScheme (sourceOpen (p := p) (q := q))
local notation "k" => Scheme.Opens.ι (sourceOpen (p := p) (q := q))

/-- Any actual original arrow with endpoints in the source union is coequalized. -/
theorem coequalizes_arrow {Y : Scheme.{u}} (a : Y ⟶ D.left) (x y : Y ⟶ B)
    (hx : a ≫ p.left = x ≫ k) (hy : a ≫ q.left = y ≫ k) :
    x ≫ projection e = y ≫ projection e := by
  have hr : ∀ z, Related p q (x z).val (y z).val := fun z ↦
    ⟨a z, congrArg (fun f ↦ f z) hx, congrArg (fun f ↦ f z) hy⟩
  apply (testCover (p := p) (q := q) x).hom_ext
  intro U
  let t := lift p.left q.left U.val.val.ι (pullback.fst x (sourceChart U) ≫ a)
    (firstChart x U) (secondChart x y hr U)
    (by rw [Category.assoc, hx, firstChart_original])
    (by rw [Category.assoc, hy, secondChart_original])
  have ht : firstChart x U ≫ (selector p q U).projection =
      secondChart x y hr U ≫ (selector p q U).projection := by
    have h := congrArg (fun f ↦ t ≫ f) (selector p q U).condition
    simpa only [t, ← Category.assoc, lift_fst, lift_snd] using h
  calc
    pullback.fst x (sourceChart U) ≫ (x ≫ projection e) =
        firstChart x U ≫ (selector p q U).projection ≫ chartMap e U := by
      rw [← firstChart_source_assoc, sourceChart_projection]
      rfl
    _ = secondChart x y hr U ≫ (selector p q U).projection ≫ chartMap e U := by
      rw [← Category.assoc, ht, Category.assoc]
    _ = pullback.fst x (sourceChart U) ≫ (y ≫ projection e) := by
      rw [← secondChart_source_assoc, sourceChart_projection]
      rfl

/-- The complete original relation on the assembled source is coequalized as schemes. -/
@[reassoc]
theorem projection_condition : fst p.left q.left k ≫ projection e =
    snd p.left q.left k ≫ projection e :=
  coequalizes_arrow e (arrow p.left q.left k) _ _
    (arrow_fst p.left q.left k) (arrow_snd p.left q.left k)

end FLT.Mazur.SchemeRelationOpenSelector
