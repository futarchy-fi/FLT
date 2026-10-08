/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafLocalIsoEvaluation
public import FLT.Mazur.ModuleSheafLocalIsoTransport

/-!
# Sealed evaluation of local module maps

An explicit evaluator keeps concrete sheaf and scalar instances out of
transport proofs. Its laws are proved on abstract modules before specialization.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.ModuleSheafMorphismGluing

variable {X : Scheme.{u}} {M N P Q : X.Modules}

/-- Evaluate a local map without unfolding its concrete module instances. -/
@[irreducible]
def localEval {U W : X.Opens} (a : M.over U ⟶ N.over U) (h : W ≤ U)
    (s : Γ(M, W)) : Γ(N, W) := localApp a h s

/-- Evaluation respects equations between local morphisms. -/
lemma localEval_congr {U W : X.Opens} {a b : M.over U ⟶ N.over U}
    (hab : a = b) (h : W ≤ U) (s : Γ(M, W)) : localEval a h s = localEval b h s := by
  rw [hab]

/-- Transported isomorphisms evaluate through their specified local morphism. -/
lemma localEval_of_iso_eq {A B : X.Opens} (h : A = B)
    (e : M.over A ≅ N.over A) (t : M.over B ≅ N.over B)
    (ht : t = Eq.mpr (congrArg (fun C ↦ M.over C ≅ N.over C) h.symm) e)
    (a : M.over A ⟶ N.over A) (ha : e.hom = a)
    (W : X.Opens) (hW : W ≤ B) (s : Γ(M, W)) :
    localEval t.hom hW s = localEval a (hW.trans_eq h.symm) s := by
  simpa only [localEval] using localApp_of_iso_eq_apply h e t ht a ha W hW s

/-- Sealed evaluation preserves composition of local morphisms. -/
lemma localEval_comp {U W : X.Opens} (a : M.over U ⟶ N.over U)
    (b : N.over U ⟶ P.over U) (h : W ≤ U) (s : Γ(M, W)) :
    localEval (a ≫ b) h s = localEval b h (localEval a h s) := by
  simpa only [localEval] using localApp_comp_apply a b h s

/-- Sealed evaluation of conjugation is conjugation on sections. -/
lemma localEval_conjugate (U : X.Opens) (a : M ≅ N) (b : P ≅ Q)
    (e : N.over U ≅ Q.over U) (W : X.Opens) (h : W ≤ U) (s : Γ(M, W)) :
    localEval (((SheafOfModules.overFunctor X.ringCatSheaf U).mapIso a ≪≫ e ≪≫
      ((SheafOfModules.overFunctor X.ringCatSheaf U).mapIso b).symm).hom) h s =
      b.inv.app W (localEval e.hom h (a.hom.app W s)) := by
  simpa only [localEval] using localApp_iso_conjugate U a b e W h s

end FLT.Mazur.ModuleSheafMorphismGluing

namespace FLT.Mazur.ModuleSheafOpenImmersionLocalHom

open ModuleSheafMorphismGluing

/-- Normalized refinement retains sealed section evaluation. -/
lemma localEval_normalize {X Y Z : Scheme.{u}}
    (i : Y ⟶ X) [IsOpenImmersion i] {M N : X.Modules}
    (t : Z ⟶ Y) [IsOpenImmersion t] (r : Z ⟶ X) [IsOpenImmersion r]
    (h : t ≫ i = r) (a : (pullback i).obj M ⟶ (pullback i).obj N)
    (W : X.Opens) (hW : W ≤ r.opensRange) (s : Γ(M, W)) :
    localEval (localHom r (SheafPullbackMapNormalization.normalize t i i r r h h a)) hW s =
      localEval (localHom i a) (hW.trans (normalizedRange_le i t r h)) s := by
  simpa only [localEval] using localHom_normalize_app_apply i t r h a W hW s

end FLT.Mazur.ModuleSheafOpenImmersionLocalHom
