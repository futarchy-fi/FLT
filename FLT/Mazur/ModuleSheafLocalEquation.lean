/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafLocalEvaluation

/-!
# Recovering pullback equations from sealed section evaluation

Local evaluation detects equality, and equations between global projections
on an open image recover equations between their genuine pullbacks.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.ModuleSheafMorphismGluing

variable {X : Scheme.{u}} {M N P : X.Modules}

/-- Sealed evaluation of a restricted global morphism is its ordinary section map. -/
lemma localEval_over (a : M ⟶ N) {U W : X.Opens} (h : W ≤ U) (s : Γ(M, W)) :
    localEval (a.over U) h s = a.app W s := by
  simp only [localEval]
  rfl

/-- Sealed evaluation detects equality of local module morphisms. -/
lemma localEval_hom_ext {U : X.Opens} {a b : M.over U ⟶ N.over U}
    (h : ∀ (W : X.Opens) (hW : W ≤ U) (s : Γ(M, W)),
      localEval a hW s = localEval b hW s) : a = b := by
  apply SheafOfModules.hom_ext
  ext V s
  unfold localEval at h
  exact h V.unop.left (leOfHom V.unop.hom) s

/-- A local equation with global outer maps can be evaluated without unfolding the modules. -/
lemma localEval_projection {U W : X.Opens} (p : M ⟶ N) (q : M ⟶ P)
    (a : N.over U ⟶ P.over U) (ha : p.over U ≫ a = q.over U)
    (hW : W ≤ U) (s : Γ(M, W)) : localEval a hW (p.app W s) = q.app W s := by
  have h := localEval_congr ha hW s
  rw [localEval_comp, localEval_over, localEval_over] at h
  exact h

end FLT.Mazur.ModuleSheafMorphismGluing

namespace FLT.Mazur.ModuleSheafOpenImmersionLocalHom

open ModuleSheafMorphismGluing

/-- Section equations on an immersion image imply the genuine pullback projection equation. -/
lemma pullback_projection_of_localEval {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsOpenImmersion i] {M N P : X.Modules} (p : M ⟶ N) (q : M ⟶ P)
    (a : (pullback i).obj N ⟶ (pullback i).obj P)
    (h : ∀ (W : X.Opens) (hW : W ≤ i.opensRange) (s : Γ(M, W)),
      localEval (localHom i a) hW (p.app W s) = q.app W s) :
    (pullback i).map p ≫ a = (pullback i).map q := by
  apply localHom_injective i
  rw [localHom_comp, localHom_map, localHom_map]
  apply localEval_hom_ext
  intro W hW s
  rw [localEval_comp, localEval_over, localEval_over]
  exact h W hW s

end FLT.Mazur.ModuleSheafOpenImmersionLocalHom
