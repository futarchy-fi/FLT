/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafLocalEvaluation
public import FLT.Mazur.ModuleSheafGluing
public import FLT.Mazur.ModuleSheafLocalIsoTransport

/-!
# Gluing from sealed section evaluation

An explicit evaluator keeps concrete sheaf and scalar instances out of
transport proofs. Its laws are proved on abstract modules before specialization.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.ModuleSheafGluing

open ModuleSheafMorphismGluing

variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)

/-- Construct ordinary gluing data from the equivalent sealed evaluation cocycle. -/
def ofLocalEval (obj : ∀ i, (U i).toScheme.Modules)
    (transition : ∀ i j,
      ((pushforward (U i).ι).obj (obj i)).over (U i ⊓ U j) ≅
        ((pushforward (U j).ι).obj (obj j)).over (U i ⊓ U j))
    (hc : ∀ i j k (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k)
      (s : Γ((pushforward (U i).ι).obj (obj i), W)),
      localEval (transition j k).hom (le_inf hj hk)
        (localEval (transition i j).hom (le_inf hi hj) s) =
          localEval (transition i k).hom (le_inf hi hk) s) : Data U where
  obj := obj
  transition := transition
  cocycle i j k W hi hj hk s := by
    simpa only [localEval] using hc i j k W hi hj hk s

end FLT.Mazur.ModuleSheafGluing
