/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafLocalHomNormalization
public import FLT.Mazur.ModuleSheafLocalIsoTransport

/-!
# Evaluation from explicit local isomorphism equations

Separate the equations identifying a local isomorphism and its morphism
from their evaluation on sections of an arbitrary subopen.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.ModuleSheafMorphismGluing

variable {X : Scheme.{u}} {M N P Q : X.Modules}

/-- Wrapper equations suffice to evaluate a transported local morphism. -/
lemma localApp_of_iso_eq {A B : X.Opens} (h : A = B)
    (e : M.over A ≅ N.over A) (t : M.over B ≅ N.over B)
    (ht : t = Eq.mpr (congrArg (fun C ↦ M.over C ≅ N.over C) h.symm) e)
    (a : M.over A ⟶ N.over A) (ha : e.hom = a)
    (W : X.Opens) (hW : W ≤ B) :
    localApp t.hom hW = localApp a (hW.trans_eq h.symm) := by
  subst B
  subst t
  subst a
  rfl

/-- Pointwise evaluation of a specified transported isomorphism. -/
lemma localApp_of_iso_eq_apply {A B : X.Opens} (h : A = B)
    (e : M.over A ≅ N.over A) (t : M.over B ≅ N.over B)
    (ht : t = Eq.mpr (congrArg (fun C ↦ M.over C ≅ N.over C) h.symm) e)
    (a : M.over A ⟶ N.over A) (ha : e.hom = a)
    (W : X.Opens) (hW : W ≤ B) (s : Γ(M, W)) :
    localApp t.hom hW s = localApp a (hW.trans_eq h.symm) s :=
  congrArg (fun b ↦ b s) (localApp_of_iso_eq h e t ht a ha W hW)

end FLT.Mazur.ModuleSheafMorphismGluing

namespace FLT.Mazur.ModuleSheafOpenImmersionLocalHom

open ModuleSheafMorphismGluing

/-- Normalized refinement evaluated at a section of a subopen. -/
lemma localHom_normalize_app_apply {X Y Z : Scheme.{u}}
    (i : Y ⟶ X) [IsOpenImmersion i] {M N : X.Modules}
    (t : Z ⟶ Y) [IsOpenImmersion t] (r : Z ⟶ X) [IsOpenImmersion r]
    (h : t ≫ i = r) (a : (pullback i).obj M ⟶ (pullback i).obj N)
    (W : X.Opens) (hW : W ≤ r.opensRange) (s : Γ(M, W)) :
    localApp (localHom r (SheafPullbackMapNormalization.normalize t i i r r h h a)) hW s =
      localApp (localHom i a) (hW.trans (normalizedRange_le i t r h)) s :=
  congrArg (fun b ↦ b s) (localHom_normalize_app i t r h a W hW)

end FLT.Mazur.ModuleSheafOpenImmersionLocalHom
