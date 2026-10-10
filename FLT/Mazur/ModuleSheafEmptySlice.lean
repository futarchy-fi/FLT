/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafMorphismGluing
public import Mathlib.Algebra.Category.Grp.Zero

/-!
# Module sheaves on empty slices

The sheaf condition makes sections on the empty open unique. Consequently any two
module sheaves have a unique comparison on the slice over the empty open.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.ModuleSheafEmptySlice
variable {X : Scheme.{u}}

/-- Sections on the empty open are unique. -/
lemma sections_subsingleton (M : X.Modules) (V : X.Opens) (hV : V = ⊥) :
    Subsingleton Γ(M, V) := by
  subst V
  exact AddCommGrpCat.subsingleton_of_isZero
    ((CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
      ((TopCat.Sheaf.isTerminalOfEmpty
        (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)).hom_ext _ _))

/-- Maps on an empty slice are unique. -/
lemma hom_ext (M N : X.Modules) (U : X.Opens) (hU : U = ⊥)
    (f g : M.over U ⟶ N.over U) : f = g := by
  apply SheafOfModules.hom_ext
  ext V s
  have hV : V.unop.left = ⊥ := le_bot_iff.mp (hU ▸ leOfHom V.unop.hom)
  let _ := sections_subsingleton N V.unop.left hV
  exact @Subsingleton.elim Γ(N, V.unop.left) (sections_subsingleton N _ hV) _ _

/-- The canonical comparison of any two modules on an empty slice. -/
def iso (M N : X.Modules) (U : X.Opens) (hU : U = ⊥) :
    M.over U ≅ N.over U where
  hom := 0
  inv := 0
  hom_inv_id := hom_ext M M U hU _ _
  inv_hom_id := hom_ext N N U hU _ _

end FLT.Mazur.ModuleSheafEmptySlice
