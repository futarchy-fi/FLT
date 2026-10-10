/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFppfLineDescentEquivalence
public import FLT.Mazur.SchemeLineDescentRefinement

/-!
# Base change of the actual fppf line descent equivalence

The comparison uses the previously constructed gluing functors, their chosen
recoveries, and refinement of the original overlap along a commutative square.
It applies in particular to every scheme base change of an fppf cover.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
open SchemePicard SchemeGeometricDescent
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y X' Y' : Scheme.{u}}
variable (p : Y ⟶ X) (q : Y' ⟶ X') (a : X' ⟶ X) (b : Y' ⟶ Y)
variable (w : q ≫ a = b ≫ p)
variable [Flat p] [Surjective p] [LocallyOfFinitePresentation p]
variable [Flat q] [Surjective q] [LocallyOfFinitePresentation q]

/-- Actual gluing commutes with refinement when both covering maps are fppf. -/
def lineGluingRefine :
    lineGluing p ⋙ lineBundlePullback a ≅ lineRefine p q a b w ⋙ lineGluing q :=
  Functor.isoWhiskerLeft (lineGluing p ⋙ lineBundlePullback a) (lineBaseRecovery q) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (lineGluing p) (lineCanonicalRefine p q a b w))
      (lineGluing q) ≪≫
    Functor.isoWhiskerRight (lineSourceRecovery p) (lineRefine p q a b w ⋙ lineGluing q)

/-- The comparison on a datum is exactly the composite of the chosen recovery maps. -/
lemma lineGluingRefine_hom (D : LineData p) :
    (lineGluingRefine p q a b w).hom.app D =
      (lineBaseRecovery q).hom.app ((lineBundlePullback a).obj ((lineGluing p).obj D)) ≫
        (lineGluing q).map
          ((lineCanonicalRefine p q a b w).hom.app ((lineGluing p).obj D)) ≫
        (lineGluing q).map
          ((lineRefine p q a b w).map ((lineSourceRecovery p).hom.app D)) := rfl

/-- Base change along any scheme morphism commutes with actual fppf gluing. -/
def lineGluingBaseChange (a : X' ⟶ X) :
    lineGluing p ⋙ lineBundlePullback a ≅
      lineRefine p (Limits.pullback.snd p a) a (Limits.pullback.fst p a)
        Limits.pullback.condition.symm ⋙ lineGluing (Limits.pullback.snd p a) :=
  lineGluingRefine p (Limits.pullback.snd p a) a (Limits.pullback.fst p a)
    Limits.pullback.condition.symm

end FLT.Mazur.SchemeAffineDescent
