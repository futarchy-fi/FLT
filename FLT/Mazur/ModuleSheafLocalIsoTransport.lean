/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafMorphismGluing

/-!
# Evaluating transported local isomorphisms

Changing the name of an open by equality preserves the action of a local
isomorphism on every subopen. Conjugating by global isomorphisms acts by
the corresponding conjugation of sections.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.ModuleSheafMorphismGluing

variable {X : Scheme.{u}} {M N P Q : X.Modules}

/-- Composition of local morphisms evaluates as composition of section maps. -/
lemma localApp_comp_apply {U W : X.Opens} (a : M.over U ⟶ N.over U)
    (b : N.over U ⟶ P.over U) (hW : W ≤ U) (s : Γ(M, W)) :
    localApp (a ≫ b) hW s = localApp b hW (localApp a hW s) := rfl

/-- Transporting the indexing open does not change the local section map. -/
lemma localApp_iso_cast {U V : X.Opens} (h : U = V) (e : M.over U ≅ N.over U)
    (W : X.Opens) (hW : W ≤ V) :
    localApp (cast (congrArg (fun A ↦ M.over A ≅ N.over A) h) e).hom hW =
      localApp e.hom (hW.trans_eq h.symm) := by
  subst V
  rfl

/-- A conjugated local transition acts by conjugating its section map. -/
lemma localApp_iso_conjugate (U : X.Opens) (a : M ≅ N) (b : P ≅ Q)
    (e : N.over U ≅ Q.over U) (W : X.Opens) (hW : W ≤ U) (s : Γ(M, W)) :
    localApp (((SheafOfModules.overFunctor X.ringCatSheaf U).mapIso a ≪≫ e ≪≫
      ((SheafOfModules.overFunctor X.ringCatSheaf U).mapIso b).symm).hom) hW s =
        b.inv.app W (localApp e.hom hW (a.hom.app W s)) := rfl

end FLT.Mazur.ModuleSheafMorphismGluing
