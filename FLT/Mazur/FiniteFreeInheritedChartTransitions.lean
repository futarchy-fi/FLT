/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFreeDualProjectiveRefinement

/-!
# Transitions for inherited ambient frames

Restricting ambient frames before passing to a common refinement gives the
same sheaf and dual projective transitions as direct restriction.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.FiniteFreeChartTransitions
variable {X : Scheme.{u}} (M : X.Modules)

/-- A frame inherited in two stages is the original directly restricted frame. -/
lemma refineChart_trans {U V W : X.Opens} (h : V ≤ U) (k : W ≤ V) {ι : Type u}
    (e : M.restrict U.ι ≅ SheafOfModules.free ι) :
    refineChart M k (refineChart M h e) = refineChart M (k.trans h) e :=
  (refineChart_comp M h k e).symm

/-- Common-refinement transitions are unchanged when the original frames are inherited. -/
lemma transition_inherited {U V A B W : X.Opens} (a : A ≤ U) (b : B ≤ V)
    (hA : W ≤ A) (hB : W ≤ B) {ι κ : Type u}
    (e : M.restrict U.ι ≅ SheafOfModules.free ι)
    (d : M.restrict V.ι ≅ SheafOfModules.free κ) :
    transition M hA hB (refineChart M a e) (refineChart M b d) =
      transition M (hA.trans a) (hB.trans b) e d := by
  simp only [transition, refineChart_trans]

/-- Inherited frames retain the actual dual projective transition on every affine overlap. -/
lemma dualProjectiveTransition_inherited {U V A B W : X.Opens} [IsAffine W.toScheme]
    (a : A ≤ U) (b : B ≤ V) (hA : W ≤ A) (hB : W ≤ B)
    {ι κ : Type u} [Finite ι] [Finite κ]
    (e : M.restrict U.ι ≅ SheafOfModules.free ι)
    (d : M.restrict V.ι ≅ SheafOfModules.free κ) :
    dualProjectiveTransition M hA hB (refineChart M a e) (refineChart M b d) =
      dualProjectiveTransition M (hA.trans a) (hB.trans b) e d := by
  rw [dualProjectiveTransition, dualProjectiveTransition, transition_inherited]

end FLT.Mazur.FiniteFreeChartTransitions
