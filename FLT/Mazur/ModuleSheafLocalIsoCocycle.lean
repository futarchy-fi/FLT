/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafLocalEvaluation

/-!
# Cocycle under equality transport of an open

Changing the name of the common open preserves a sectionwise cocycle.
The transport is proved with abstract modules before applying it to the
effectively descended chart sheaves.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.ModuleSheafMorphismGluing

/-- Changing the name of an open preserves sealed section evaluation. -/
theorem localEval_cast {X : Scheme.{u}} {M N : X.Modules} {U V : X.Opens}
    (h : U = V) (a : M.over U ≅ N.over U) (W : X.Opens) (hW : W ≤ V)
    (s : Γ(M, W)) :
    localEval (cast (congrArg (fun A ↦ M.over A ≅ N.over A) h) a).hom hW s =
      localEval a.hom (hW.trans_eq h.symm) s := by
  subst V
  rfl

/-- Equality of linear section maps gives equality of sealed evaluations. -/
theorem localEval_eq_of_localApp_eq {X : Scheme.{u}} {M N : X.Modules}
    {U V W : X.Opens} (a : M.over U ⟶ N.over U) (b : M.over V ⟶ N.over V)
    (hU : W ≤ U) (hV : W ≤ V) (h : localApp a hU = localApp b hV) (s : Γ(M, W)) :
    localEval a hU s = localEval b hV s := by
  simpa only [localEval] using congrArg (fun f ↦ f s) h

/-- Equality transport of all three transition isomorphisms preserves their cocycle. -/
theorem localIso_cast_cocycle_eval {X : Scheme.{u}} {M N P : X.Modules}
    {U V : X.Opens} (h : U = V)
    (a : M.over U ≅ N.over U) (b : N.over U ≅ P.over U) (c : M.over U ≅ P.over U)
    (W : X.Opens) (hW : W ≤ V) (s : Γ(M, W))
    (hc : localEval b.hom (hW.trans_eq h.symm)
        (localEval a.hom (hW.trans_eq h.symm) s) =
      localEval c.hom (hW.trans_eq h.symm) s) :
    localEval (cast (congrArg (fun A ↦ N.over A ≅ P.over A) h) b).hom hW
        (localEval (cast (congrArg (fun A ↦ M.over A ≅ N.over A) h) a).hom hW s) =
      localEval (cast (congrArg (fun A ↦ M.over A ≅ P.over A) h) c).hom hW s := by
  subst V
  exact hc

end FLT.Mazur.ModuleSheafMorphismGluing
