/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# The morphism induced on fibers over a common base

The map on actual scheme fibers is an iterated pullback projection. Its
compatibility with the original map and properness are proved directly.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.RelativeFiber

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (s : S)

/-- The actual morphism on scheme-theoretic fibers over a common base. -/
def map : (f ≫ g).fiber s ⟶ g.fiber s :=
  (pullbackRightPullbackFstIso g (S.fromSpecResidueField s) f).inv ≫
    pullback.snd f (g.fiberι s)

/-- The induced fiber morphism lies over the original morphism. -/
@[reassoc (attr := simp)]
lemma map_ι : map f g s ≫ g.fiberι s = (f ≫ g).fiberι s ≫ f := by
  simp [map, Scheme.Hom.fiberι, Category.assoc]

/-- The fiber morphism is proper whenever the original morphism is proper. -/
instance map_isProper [IsProper f] : IsProper (map f g s) := by
  unfold map
  infer_instance

/-- Compatibility on underlying points, without unfolding any pullback. -/
lemma map_apply_ι (x : (f ≫ g).fiber s) :
    g.fiberι s (map f g s x) = f ((f ≫ g).fiberι s x) :=
  congrArg (fun k : (f ≫ g).fiber s ⟶ Y ↦ k x) (map_ι f g s)

end FLT.Mazur.RelativeFiber
