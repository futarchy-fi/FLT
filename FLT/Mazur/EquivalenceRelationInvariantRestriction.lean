/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationFiberRebase

/-!
# Restricting an internal equivalence relation to an invariant subobject

A cartesian first-endpoint square and a compatible second endpoint construct
the full restricted equivalence relation. Reflexivity, inversion and
composition are lifted from the original relation, not supplied as hypotheses.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.EquivalenceRelationFiber
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {C : Type*} [Category* C] [HasPullbacks C]
  {D A E B : C} {p q : D ⟶ A} (e : CategoryTheory.EquivalenceRelation p q)
  {a : E ⟶ D} {b : B ⟶ A} {r s : E ⟶ B}
  (H : IsPullback a r p b) (hs : a ≫ q = s ≫ b) [Mono b]

include e H hs in
omit [HasPullbacks C] [Mono b] in
/-- The whole restricted relation inherits joint monicity of its endpoints. -/
theorem invariantRestriction_jointlyMono : JointlyMono₂ r s where
  right_cancellation {T} x y hr hq := by
    apply H.hom_ext
    · apply e.right_cancellation
      · rw [Category.assoc, Category.assoc, H.w, ← Category.assoc,
          ← Category.assoc, hr]
      · rw [Category.assoc, Category.assoc, hs, ← Category.assoc,
          ← Category.assoc, hq]
    · exact hr

/-- Restrict the original reflexive arrow by the full cartesian first-endpoint square. -/
def invariantRestrictionRefl : B ⟶ E :=
  H.lift (b ≫ e.r) (𝟙 B) (by simp)

/-- Restrict original inversion, retaining every arrow above the invariant domain. -/
def invariantRestrictionSwap : E ⟶ E :=
  H.lift (a ≫ e.s) s (by rw [Category.assoc, e.symmetry₁, hs])

/-- Restrict original composition on the entire pair of composable restricted arrows. -/
def invariantRestrictionComp : pullback s r ⟶ E :=
  H.lift (compose e (pullback.fst s r ≫ a) (pullback.snd s r ≫ a) (by
    rw [Category.assoc, hs, ← Category.assoc, pullback.condition,
      Category.assoc, ← H.w, ← Category.assoc]))
    (pullback.fst s r ≫ r) (by rw [compose_fst, Category.assoc, H.w, Category.assoc])

/-- The unchanged relation restricts to a genuine internal equivalence relation. -/
def invariantRestrictionEquivalence : CategoryTheory.EquivalenceRelation r s where
  toJointlyMono₂ := invariantRestriction_jointlyMono e H hs
  r := invariantRestrictionRefl e H
  reflexivity₁ := H.lift_snd _ _ _
  reflexivity₂ := by
    apply (cancel_mono b).mp
    rw [Category.id_comp, Category.assoc, ← hs, ← Category.assoc,
      invariantRestrictionRefl, H.lift_fst, Category.assoc, e.reflexivity₂,
      Category.comp_id]
  s := invariantRestrictionSwap e H hs
  symmetry₁ := H.lift_snd _ _ _
  symmetry₂ := by
    apply (cancel_mono b).mp
    rw [Category.assoc, ← hs, ← Category.assoc, invariantRestrictionSwap,
      H.lift_fst, Category.assoc, e.symmetry₂, H.w]
  c := pullback.cone s r
  isLimit := pullback.isLimit s r
  t := invariantRestrictionComp e H hs
  transitivity₁ := H.lift_snd _ _ _
  transitivity₂ := by
    apply (cancel_mono b).mp
    rw [Category.assoc, ← hs, ← Category.assoc, invariantRestrictionComp,
      H.lift_fst, compose_snd, Category.assoc, hs, Category.assoc]
    rfl

end FLT.Mazur.EquivalenceRelationFiber
