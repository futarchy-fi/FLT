/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafProjectionSections

/-!
# Scalar action in specified projection coordinates

Projection sections retain the original scalar pullback, including the specified
preimage identification. For a direct image this is the composite scheme map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.ModuleSheafProjectionSections

variable {X Y : Scheme.{u}} (i : Y ⟶ X) (G : X.Modules) (M : Y.Modules)
  (q : G ⟶ (pushforward i).obj M)

/-- Specified projection coordinates retain the original pullback of scalars. -/
lemma sections_smul (W : X.Opens) (U : Y.Opens) (h : i ⁻¹ᵁ W = U)
    (r : Γ(X, W)) (s : Γ(G, W)) :
    sections i G M q W U h (r • s) =
      (i.appLE W U (le_of_eq h.symm) r) • sections i G M q W U h s := by
  change M.presheaf.map (eqToHom h.symm).op (q.app W (r • s)) = _
  rw [Hom.app_smul]
  exact M.map_smul (eqToHom h.symm) (i.app W r) (q.app W s)

/-- Source scalars of a direct image act by the original composite scheme morphism. -/
lemma sections_pushforward_smul {Z : Scheme.{u}} (p : X ⟶ Z)
    (V : Z.Opens) (U : Y.Opens) (h : i ⁻¹ᵁ (p ⁻¹ᵁ V) = U)
    (r : Γ(Z, V)) (s : Γ((pushforward p).obj G, V)) :
    sections i G M q (p ⁻¹ᵁ V) U h (r • s) =
      ((i ≫ p).appLE V U (le_of_eq h.symm) r) •
        sections i G M q (p ⁻¹ᵁ V) U h s := by
  exact sections_smul i G M q (p ⁻¹ᵁ V) U h (p.app V r) s

end FLT.Mazur.ModuleSheafProjectionSections
