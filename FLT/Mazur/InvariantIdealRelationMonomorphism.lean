/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.InvariantIdealRelation
public import Mathlib.CategoryTheory.EquivalenceRelation

/-!
# Joint monicity on the whole invariant closed boundary

Restricting a jointly monic relation to an invariant ideal preserves joint
monicity of its two full closed endpoints. No reduced boundary is substituted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.InvariantIdealRelation
set_option backward.isDefEq.respectTransparency false
variable {X D : Scheme.{u}} (I : X.IdealSheafData) (p q : D ⟶ X)
  (h : I.comap p = I.comap q) [JointlyMono₂ p q]

/-- The original two endpoints still distinguish all arrows on the entire closed boundary. -/
instance endpoints_jointlyMono :
    JointlyMono₂ (pullback.snd p I.subschemeι) (snd I p q h) where
  right_cancellation := by
    intro T a b ha hb
    apply pullback.hom_ext
    · apply JointlyMono₂.right_cancellation (p₁ := p) (p₂ := q)
      · simpa only [Category.assoc, ← pullback.condition] using
          congrArg (fun k ↦ k ≫ I.subschemeι) ha
      · simpa only [Category.assoc, snd_ι] using
          congrArg (fun k ↦ k ≫ I.subschemeι) hb
    · exact ha

end FLT.Mazur.InvariantIdealRelation
