/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafLocalEvaluation

/-!
# Evaluating naturality squares on open subsets

A commuting square of slice maps evaluates on every subopen. Global maps
retain their ordinary section action through the sealed evaluator.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.ModuleSheafMorphismGluing
variable {X : Scheme.{u}} {M N P Q : X.Modules}

/-- A restricted global morphism evaluates by its original section map. -/
lemma localEval_over (f : M ⟶ N) {U V : X.Opens} (h : V ≤ U) (s : Γ(M, V)) :
    localEval (f.over U) h s = f.app V s := by
  unfold localEval
  rfl

/-- A commuting square on a slice gives a commuting square on every subopen. -/
lemma localEval_naturality {U V : X.Opens} (h : V ≤ U)
    (a : M.over U ⟶ P.over U) (b : N.over U ⟶ Q.over U)
    (f : M ⟶ N) (g : P ⟶ Q) (w : f.over U ≫ b = a ≫ g.over U)
    (s : Γ(M, V)) :
    localEval b h (f.app V s) = g.app V (localEval a h s) := by
  have hw := localEval_congr w h s
  simpa only [localEval_comp, localEval_over] using hw

end FLT.Mazur.ModuleSheafMorphismGluing
